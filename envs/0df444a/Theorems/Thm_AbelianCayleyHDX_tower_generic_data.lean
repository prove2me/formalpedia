-- Prove2me | Theorems.Thm_AbelianCayleyHDX_tower_generic_data
-- name    : AbelianCayleyHDX.tower_generic_data
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T00:33:35.427931+00:00
-- url     : https://prove2.me/theorems/b4f80b3e-2513-4e67-a6cf-89e85edf4eaa
-- title:
--   Evaluation data from the Garcia–Stichtenoth tower, with a 1-generic matrix of linear forms (Lemma 4.1, Sec. 4.1–4.2)
-- statement:
--   Fix $q=2^h\ge8$ and a field $F$ with $q^2$ elements, and set up the data of Sections 4.1–4.2 at a level of the Garcia–Stichtenoth tower of genus $g$. Concretely: the $\nu=(q-2)g$ evaluation vectors $e_{P_a}\in F^t$, where $t=2g+1$, and the $k\times m$ matrix of linear forms $L_{ij}(x)=x(u_iz_j)$, where $k=\lfloor g/4\rfloor$ and $m=3k$. Then:
--
--   1. the $e_{P_a}$ span $F^t$, are nonzero, and are pairwise non-proportional;
--   2. every nonzero linear functional vanishes at no more than $3g$ of them;
--   3. $L_{ij}(e_P)=u_i(P)z_j(P)$ at every selected point;
--   4. the matrix is **1-generic** over the algebraic closure $\bar F$: for nonzero $\alpha\in\bar F^{k}$ and $\beta\in\bar F^{m}$, the generalized entry $\sum_{i,j}\alpha_i\beta_jL_{ij}$ is a nonzero linear form;
--   5. the vectors $e_{P_a}$ are computable in time polynomial in $t$.
--
--   Clause 4 is the first step of the proof of Proposition 4.6. The generalized entry is evaluation at the product $(\sum_i\alpha_iu_i)(\sum_j\beta_jz_j)$. Both factors are nonzero, because the bases stay linearly independent after scalar extension, and their product is nonzero because the curve stays integral over $\bar F$.
--
--   In the formal statement, for every $g_0$ there is a sequence of genera $g_j\to\infty$, all at least $g_0$, carrying such data, and for every encoding of $F$ one Turing machine lists the vectors $e_{P_a}$ in time polynomial in $t_j$.
--
--   **Formalization Note** A linear form is identified with its coefficient vector $(L_{ij}(e_r))_r$, and 1-genericity says that the coefficient vector of the generalized entry is nonzero. $\bar F$ is `AlgebraicClosure F`.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 4.1 and Section 4.1 (p.15), Section 4.2 (p.16), proof of Proposition 4.6 ('Thus M is 1-generic', p.17); Garcia–Stichtenoth (1996); Guruswami–Xing (2022)

import Mathlib
import Definitions.Def_AbelianCayleyHDX_encFVec
import Definitions.Def_HMBinPacking_OutputsWithin
open Filter RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX

/-- **Section 4.1–4.2 and Proposition 4.6 (1-generic form): evaluation data from the Garcia–Stichtenoth tower**
(Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937
(held version, sha256 6f5b0daa…75ba), Lemma 4.1, the construction of Section 4.1 (p.15), the matrix
of linear forms of Section 4.2 (p.16) and Proposition 4.6 (p.17)). Fix `q = 2^h ≥ 8` and `F = 𝔽_{q²}`.
At a level of the Garcia–Stichtenoth tower of genus `g ≥ 4` with `|P_r| ≥ (q − 2)g`, choose
`ν = (q − 2)g` rational points `P_1, …, P_ν`, put `G = 3gP_∞`, `W = L(G)`, `t = dim W = 2g + 1`, and
identify `W^∨ ≅ F^t`; let `e_P ∈ W^∨` be evaluation at `P`. With `k = ⌊g/4⌋`, `m = 3k`, bases
`u_1, …, u_k` of `U ≤ L((g + k)P_∞)` and `z_1, …, z_m` of `V ≤ L(G − (g + k)P_∞)`, let
`L_{ij}(x) = x(u_i z_j)` for `x ∈ W^∨`. The paper shows:
1. the `e_P` span `W^∨`, are nonzero and pairwise non-proportional (p.15);
2. every nonzero `s ∈ W` (a nonzero functional on `W^∨`) vanishes at no more than `3g` of the
   selected points (p.15);
3. `L_{ij}(e_P) = u_i(P) z_j(P)` (rank one at every selected point; Eq. (4.1));
4. the matrix of linear forms is 1-generic over the algebraic closure `F̄`: for nonzero
   `α ∈ F̄^k`, `β ∈ F̄^m` the generalized entry `∑ αᵢ βⱼ L_{ij}` is a nonzero linear form
   (Proposition 4.6, first paragraph: `(∑ αᵢuᵢ)(∑ βⱼzⱼ) ≠ 0` since `X_{F̄}` is integral);
5. the points (as vectors of `F^t`) are computable in time polynomial in `t` ([GX22], p.15).

Stated as: for every `g₀` there is a sequence of genera `g_j → ∞`, all `≥ g₀`, with vectors
`e_j : Fin ((q − 2) g_j) → F^{2g_j + 1}` and linear forms `L_j` with these properties, and for every
encoding `enc` of `F` one machine outputs `t_j = 2g_j + 1` and the list of the `e_j(a)` within
time polynomial in `t_j`.

**Formalization Note** The curve, the tower and the Riemann–Roch spaces are not formalized; this
statement records their consequences used in Section 4.3 in coordinates. "For every `g₀`" reflects
"discarding finitely many earlier tower levels" (p.17). -/
theorem tower_generic_data (h : ℕ) (hq : 8 ≤ 2 ^ h) (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (hF : Fintype.card F = (2 ^ h) ^ 2) (g₀ : ℕ) :
    ∃ g : ℕ → ℕ, Tendsto g atTop atTop ∧ (∀ j, g₀ ≤ g j) ∧
    ∃ (e : ∀ j, Fin ((2 ^ h - 2) * g j) → (Fin (2 * g j + 1) → F))
      (L : ∀ j, Fin (g j / 4) → Fin (3 * (g j / 4)) → Module.Dual F (Fin (2 * g j + 1) → F)),
      (∀ j,
        Submodule.span F (Set.range (e j)) = ⊤ ∧
        (∀ a, e j a ≠ 0) ∧
        (∀ a b, a ≠ b → ∀ c : F, e j a ≠ c • e j b) ∧
        (∀ c : Module.Dual F (Fin (2 * g j + 1) → F), c ≠ 0 →
          (Finset.univ.filter fun a => c (e j a) = 0).card ≤ 3 * g j) ∧
        (∀ a, ∃ (u : Fin (g j / 4) → F) (z : Fin (3 * (g j / 4)) → F),
          ∀ i l, L j i l (e j a) = u i * z l) ∧
        (∀ (α : Fin (g j / 4) → AlgebraicClosure F) (β : Fin (3 * (g j / 4)) → AlgebraicClosure F),
          α ≠ 0 → β ≠ 0 → ∃ r : Fin (2 * g j + 1),
            ∑ i, ∑ l, α i * β l * algebraMap F (AlgebraicClosure F) (L j i l (Pi.single r 1)) ≠ 0)) ∧
      ∀ enc : F ≃ Fin (Fintype.card F), ∃ M : Turing.TM2ComputableAux Bool Bool,
        ∃ p : Polynomial ℕ, ∀ j,
          HMBinPacking.OutputsWithin M (encNat j)
            (encNat (2 * g j + 1) ++ encList (encFVec enc) (List.ofFn (e j)))
            (p.eval (2 * g j + 1)) := by sorry

end AbelianCayleyHDX
