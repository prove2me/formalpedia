-- Prove2me | Theorems.Thm_DisjointPathsDAG_lemma_3_4
-- name    : DisjointPathsDAG.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:45.082811+00:00
-- url     : https://prove2.me/theorems/2e280b37-097d-47c8-b43b-a333d0154623
-- title:
--   Lemma 3.4 (Correlated extraction step)
-- statement:
--   There are constants $C$, $A$ and one machine program such that the following holds over every finite field $F$. Let $(L,U)$ be a monotone cut of a regional instance $\mathcal R$ (terminals in $R$), with $j$ active labels and $|F|\ge2j$; let $\xi\in F^E$ satisfy $F_R(\xi)\neq0$; let $P$ be a division-free program of size $S$ computing $F_R$; and let $Q$ be $F_R$ with the noncut variables fixed to $\xi$. Then:
--
--   1. $Q\neq0$, and for every set $B$ of $j$ cut edges with $[z^B]Q\neq0$ there are at most $j!$ feasible bijections $J\to B$, and one of them, $\sigma$, has $F^\sigma_L(\xi)\neq0$ and $F^\sigma_U(\xi)\neq0$;
--   2. the program, run on the cut, $P$ and $\xi$, has expected running time at most $C\,(j^2+1)\,S$, uses at most $C\,S$ cells, never changes the cells holding $\xi$, and every halting run outputs a set $B$ of $j$ cut edges with $[z^B]Q\neq0$.
--
--   Evaluating the child polynomials for the feasible bijections onto $B$ then finds $\sigma$. This is one step of every reporting recursion in the paper.
--
--   Differences from the source:
--   - reading: "B and σ can be found using expected O((j²+1)S) field operations and O(S) space, plus the evaluation at ξ of the child polynomials" → the machine finds $B$ within the bound; clause 1 gives a feasible $\sigma$ onto $B$ with nonzero child evaluations; reason: the child evaluations are the separately charged cost
--   - reading: field operations → machine steps; reason: every instruction is counted, the stronger reading
--   - encoding: "never changes ξ" → the field cells holding $\xi$ keep their values at every step; reason: the machine of Section 2.1
--   - encoding: $O(S)$ space → `spaceUsed ≤ C * S`; reason: cells whose content changes; the input is not charged
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Lemma 3.4 (Correlated extraction step), pp.9–10

import Mathlib
import Definitions.Def_DisjointPathsDAG_Encoding

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace DisjointPathsDAG

open MvPolynomial

open Classical in
/-- Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Lemma 3.4 (Correlated extraction step),
pp.9–10: "Let (L, U) be a monotone cut of a regional instance R, let ξ ∈ F^E satisfy FR(ξ) ≠ 0, and
suppose that FR has a division-free circuit of size S and |F| ≥ 2j. A set B of j cut edges and a
feasible bijection σ: J → B with FσL(ξ) ≠ 0 and FσU(ξ) ≠ 0 can be found using expected O((j2 + 1)S)
field operations and O(S) space, plus the evaluation at ξ of the child polynomials for the at most j!
feasible bijections. The computation never changes ξ."

There are constants `C`, `A` and one machine program `Prog` such that, over every finite field `F`, in
the setting of Section 3, for every monotone cut `(L, U)` of a regional instance `ρ` (terminals in `R`),
every `ξ` with `F_R(ξ) ≠ 0`, and every program `P` of size `S` (constants `cs`) computing `F_R` as a
formal polynomial (variable `e` = input `e`), with `2j ≤ |F|`, `j = |J|`, and `Q` the polynomial `F_R`
with the noncut variables fixed to `ξ`:
1. `Q ≠ 0`, and for every set `B` of `j` cut edges with nonzero coefficient of `z^B` in `Q`, some
   feasible bijection `σ : J ≃ B` has `F^σ_L(ξ) ≠ 0` and `F^σ_U(ξ) ≠ 0` (at most `j!` bijections are
   feasible), so evaluating the child polynomials for the feasible bijections finds such a `σ`;
2. run on `(j, M, cut bits, P; ξ, cs)`, `Prog` has expected running time at most `C · (j² + 1) · S`, uses
   at most `C · S` cells on every run, never changes the field cells holding `ξ`, and every halting run
   outputs the indices of a set `B` of `j` distinct cut edges whose monomial has a nonzero coefficient
   in `Q`.

**Formalization Note** "Plus the evaluation at ξ of the child polynomials" is rendered as follows: the
machine returns `B` within the stated bound, and clause 1 says that among the feasible bijections onto
`B` (at most `j!`) one has both child evaluations nonzero; the child evaluations are the separately
charged cost. Every machine instruction counts as one operation. -/
theorem lemma_3_4 :
    ∃ (C : ℝ) (A : ℕ) (Prog : Program), 0 < C ∧ 1 ≤ A ∧
      ∀ (F : Type) [Field F] [Fintype F] (V : Type) [Fintype V] [DecidableEq V] (M k : ℕ)
        (ends : Fin M → V × V) (H : Fin k → Set (Fin M × Bool)) (ρ : RegInst V k) (L U : Finset V)
        (ξ : Fin M → F) (P : SLP) (cs : List F),
        ρ.WF → IsMonotoneCut ends H ρ L U → eval ξ (regionalPoly F ends H ρ) ≠ 0 →
        P.formalOut (fun c => cs.getD c 0) 0 = rename Fin.val (regionalPoly F ends H ρ) →
        2 * (activeSet ρ L).card ≤ Fintype.card F →
        (cutRestrict ends L U ξ (regionalPoly F ends H ρ) ≠ 0 ∧
          ∀ B : Finset (Fin M), B ⊆ cutEdges ends L U → B.card = (activeSet ρ L).card →
            (cutRestrict ends L U ξ (regionalPoly F ends H ρ)).coeff (setExp B) ≠ 0 →
            ((Finset.univ : Finset (activeSet ρ L ≃ B)).filter (IsFeasibleBij ends H ρ L)).card ≤
              (activeSet ρ L).card.factorial ∧
            ∃ σ : activeSet ρ L ≃ B, IsFeasibleBij ends H ρ L σ ∧
              eval ξ (regionalPoly F ends H (lowChild ends ρ L σ)) ≠ 0 ∧
              eval ξ (regionalPoly F ends H (highChild ends ρ L U σ)) ≠ 0) ∧
        (Measurable (fun ω => (haltTime (wordWidth A (extractInput ends L U (activeSet ρ L).card P ξ cs).size)
            F Prog (extractInput ends L U (activeSet ρ L).card P ξ cs) ω : ℝ≥0∞)) ∧
          ∫⁻ ω, (haltTime (wordWidth A (extractInput ends L U (activeSet ρ L).card P ξ cs).size) F Prog
              (extractInput ends L U (activeSet ρ L).card P ξ cs) ω : ℝ≥0∞) ∂(tapeLaw F) ≤
            ENNReal.ofReal (C * (((activeSet ρ L).card : ℝ) ^ 2 + 1) * P.size) ∧
          (∀ ω : Tape F, (spaceUsed (wordWidth A (extractInput ends L U (activeSet ρ L).card P ξ cs).size)
            F Prog (extractInput ends L U (activeSet ρ L).card P ξ cs) ω : ℝ≥0∞) ≤
              ENNReal.ofReal (C * P.size)) ∧
          (∀ (ω : Tape F) (t : ℕ) (e : Fin M),
            (stateAt (wordWidth A (extractInput ends L U (activeSet ρ L).card P ξ cs).size) F Prog
              (extractInput ends L U (activeSet ρ L).card P ξ cs) ω t).Fc e = ξ e) ∧
          ∀ (ω : Tape F) (t : ℕ),
            HaltsAt (wordWidth A (extractInput ends L U (activeSet ρ L).card P ξ cs).size) F Prog
              (extractInput ends L U (activeSet ρ L).card P ξ cs) ω t →
            ∃ B : Finset (Fin M), B ⊆ cutEdges ends L U ∧ B.card = (activeSet ρ L).card ∧
              (outWords (extractInput ends L U (activeSet ρ L).card P ξ cs)
                (stateAt (wordWidth A (extractInput ends L U (activeSet ρ L).card P ξ cs).size) F Prog
                  (extractInput ends L U (activeSet ρ L).card P ξ cs) ω t)).Nodup ∧
              (outWords (extractInput ends L U (activeSet ρ L).card P ξ cs)
                (stateAt (wordWidth A (extractInput ends L U (activeSet ρ L).card P ξ cs).size) F Prog
                  (extractInput ends L U (activeSet ρ L).card P ξ cs) ω t)).toFinset = B.image Fin.val ∧
              (cutRestrict ends L U ξ (regionalPoly F ends H ρ)).coeff (setExp B) ≠ 0) := by sorry

end DisjointPathsDAG
