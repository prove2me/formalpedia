-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_Supplement_proposition_11
-- name    : ChvatalOneHard398.SAT.Supplement.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:29:43.543853+00:00
-- url     : https://prove2.me/theorems/a1f80dba-07ff-4ae3-a160-0490034c3d51
-- title:
--   Proposition 11 — bounded basis and feasibility laws
-- statement:
--   Let $n>0$, let $q$ be prime, let $k=\lceil\log_2q\rceil$ and $m=3nk$, and assume $q>16m^2$. Put $r=\lfloor(q-1)/(16m^2)\rfloor$. A fixed deterministic polynomial-time construction produces from every residue matrix $A$ a nonsingular integral basis $B(A)$ of $\Lambda_q(A^T)$ with every entry in $\{0,\ldots,q\}$. The polynomial bounds are uniform in $n$ and $\log q$.
--
--   Let $\chi$ be any probability law on $\mathbb Z$, and let $\varepsilon_\chi=\Pr_{e\sim\chi^m}\{\|e\|_\infty>r\}$. For $Q=Q(B(A),t,r)$, both the LWE and uniform input laws give
--   $$\Pr\{Q\text{ is thin}\}\ge1-2^{-2nk}.$$
--   For the LWE law and uniform law respectively,
--   $$\Pr_{\rm LWE}\{Q\cap\mathbb Z^m\ne\varnothing\}\ge1-\varepsilon_\chi,\qquad
--   \Pr_{\rm unif}\{Q\cap\mathbb Z^m\ne\varnothing\}\le2^{-m}.$$
--
--   The law is unconditioned on thinness, and the error distribution is arbitrary. These are the construction and all probability guarantees needed for Theorem 12.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time computations → the published binary TM2 next-step model and finite input records; reason: uniform time bounds charge for writing every query and output on every raw input
--   - encoding: uniform residues, independent errors and probabilities → canonical integral residues and genuine PMFs with nonnegative mass sums; reason: no rank conditioning, integrability defaults or nonmeasurable maps are introduced
--   - encoding: a lattice and error vector in dimension m=3nk → an explicit n>0 premise; reason: zero-dimensional first minima and the printed radius denominator are outside the source domain
--   - encoding: the Hermite-normal-form basis of [A^T | qI] → explicit extended-gcd row-Hermite elimination of the transposed generators; reason: the resulting lower-triangular reduced basis is the same canonical Hermite basis; its correctness and entry bounds remain conclusions
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.14, Proposition 11. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Supplement_Probability

namespace ChvatalOneHard398.SAT.Supplement
open scoped BigOperators
open CombOpt.ChvatalRank

theorem proposition_11 :
    PolyTime encAryMatrix id (fun a => encBasis a (basisMatrix a)) ∧
    ∀ (n q : ℕ), 0 < n → q.Prime →
      let m := samples n q
      16*m^2 < q →
      (∀ A : Matrix (Fin n) (Fin m) ℤ,
        (∀ i j, 0 ≤ A i j ∧ A i j < (q : ℤ)) →
        let a : AryMatrix := ⟨n,m,q,A⟩
        (∀ i j, 0 ≤ basisMatrix a i j ∧ basisMatrix a i j ≤ (q : ℤ)) ∧
        (basisMatrix a).det ≠ 0 ∧ zLattice (basisMatrix a) = aryLattice a) ∧
      (∀ χ : PMF ℤ,
        (1-(2 : ℝ)^(-((2*n*bits q : ℕ) : ℤ)) ≤
          prob (lweLaw n m q χ) (fun a => (toPara a).Thin)) ∧
        (1-(2 : ℝ)^(-((2*n*bits q : ℕ) : ℤ)) ≤
          prob (uniformLaw n m q) (fun a => (toPara a).Thin)) ∧
        (1-prob (iid χ m) (fun e => ∃ j, radius m q < |e j|) ≤
          prob (lweLaw n m q χ) (fun a => (toPara a).Feasible)) ∧
        (prob (uniformLaw n m q) (fun a => (toPara a).Feasible) ≤
          (2 : ℝ)^(-(m : ℤ)))) := by sorry

end ChvatalOneHard398.SAT.Supplement
