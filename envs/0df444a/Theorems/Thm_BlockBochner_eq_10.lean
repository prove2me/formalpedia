-- Prove2me | Theorems.Thm_BlockBochner_eq_10
-- name    : BlockBochner.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:41:51.371205+00:00
-- url     : https://prove2.me/theorems/f6256ea2-32f6-41d2-bf84-1e2c0e4069ec
-- title:
--   Eq. (10) — $\tilde B\succeq\alpha\tilde D$
-- statement:
--   Let $H$ be a real Hilbert space, $W_1,\dots,W_n$ closed subspaces with orthogonal projections $P_i$, $P_{ij}$ the projection onto $W_i\cap W_j$, and $S=(s_{ij})$ a real symmetric matrix with non-negative entries, zero diagonal and $\lambda_{\max}(S)<1$ such that $\|P_iP_j-P_{ij}\|\le s_{ij}$ for all $i\ne j$. Let $M=I-S$ and let $B$ be the Bochner operator on $H_1=\bigoplus_iW_i$.
--   Let $T_1,\dots,T_m\subseteq[n]$ be disjoint nonempty subsets, $T=\bigsqcup_aT_a$, $C=((M^{-1})_T)^{-1}$, $D=\mathrm{blockdiag}(C_{T_1},\dots,C_{T_m})$ and $\alpha=\lambda_{\min}(D^{-1/2}CD^{-1/2})$. Let $\tilde B=((B^{-1})_{TT})^{-1}$ on $H^T_1=\bigoplus_{i\in T}W_i$ and $\tilde D=\mathrm{blockdiag}(\tilde B_{T_1T_1},\dots,\tilde B_{T_mT_m})$. Then
--   $$\tilde B\succeq\alpha\tilde D\qquad\text{on }H^T_1.\tag{10}$$
--
--   **Formalization Note** $\tilde B$ and $\tilde D$ are extended by zero to $H_1$, and the inequality of quadratic forms is asserted for $g\in H^T_1$.
--
--   Differences from the source:
--   - encoding: B̃, D̃ operators on H^T_1 → extended by zero to ⊕_i W_i, inequality for g ∈ H^T_1; reason: the quadratic forms on H^T_1 are unchanged
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 3.3, Eq. (10), p.25

import Mathlib
import Definitions.Def_BlockBochner_Dtilde
import Definitions.Def_BlockBochner_IsAdmissible
import Definitions.Def_BlockBochner_lamMin
import Definitions.Def_BlockBochner_matD
import Definitions.Def_BlockBochner_invSqrt

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Eq. (10), coercivity-type inequality for `B̃`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 3.3, Eq. (10), p.25: `B̃ ⪰ α D̃`,
where `B̃ = ((B⁻¹)_{TT})⁻¹` on `H^T_1 = ⊕_{i∈T} W_i`, `D̃ = blockdiag(B̃_{T₁T₁}, …, B̃_{T_mT_m})`, and
`α = λ_min(D^{−1/2} C D^{−1/2})` with `C = ((M⁻¹)_T)⁻¹`, `D = blockdiag(C_{T₁}, …, C_{T_m})`.

Setting of Sec. 3.2 (p.21): `H` a real Hilbert space, `W₁, …, W_n` closed subspaces with orthogonal
projections `P_i`, `P_{ij}` the projection onto `W_i ∩ W_j`, and `S` a real symmetric matrix with
non-negative entries, zero diagonal and `λ_max(S) < 1` such that `‖P_i P_j − P_{ij}‖ ≤ s_{ij}` for all
`i ≠ j`; `M = I − S`. `T₁, …, T_m ⊂ [n]` are disjoint nonempty subsets and `T = ⊔_a T_a`.

**Formalization Note** `B̃` and `D̃` are extended by zero to `⊕_i W_i` (`Btilde`, `Dtilde`), and the
inequality of quadratic forms is asserted on `H^T_1 = coordSub W T`. -/
theorem eq_10 {n : ℕ} (W : Fin n → ClosedSubmodule ℝ H) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : IsAdmissible S)
    (hang : ∀ i j, i ≠ j → ‖(W i : Submodule ℝ H).starProjection ∘L (W j : Submodule ℝ H).starProjection -
      ((W i ⊓ W j : ClosedSubmodule ℝ H) : Submodule ℝ H).starProjection‖ ≤ S i j)
    {m : ℕ} (T : Fin m → Finset (Fin n)) (hT : Pairwise fun a b => Disjoint (T a) (T b))
    (hTne : ∀ a, (T a).Nonempty)
    (g : PiLp 2 (fun i => (W i : Submodule ℝ H))) (hg : g ∈ coordSub W (blockUnion T : Set (Fin n))) :
    lamMin (invSqrt (matD S T) * matC S T * invSqrt (matD S T)) * inner ℝ g (Dtilde W T g) ≤
      inner ℝ g (Btilde W (blockUnion T : Set (Fin n)) g) := by sorry

end BlockBochner
