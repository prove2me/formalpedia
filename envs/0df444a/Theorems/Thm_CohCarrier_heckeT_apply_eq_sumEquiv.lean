-- Prove2me | Theorems.Thm_CohCarrier_heckeT_apply_eq_sumEquiv
-- name    : CohCarrier.heckeT_apply_eq_sumEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/06142304-2cd2-5d18-8911-e3c5cd4078a8
-- title:
--   Hecke operator T_ℓ as a coset-indexed sum
-- statement:
--   Fix $M \in \mathbb{N}$, a subgroup $H \le (\mathbb{Z}/M)^\times$ and a nonzero $\ell \in \mathbb{N}$. Here $\Gamma_H(M) =$ `GammaH M H` is the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of the elements of $\Gamma_0(M)$ whose associated unit (the lower-right entry mod $M$, via `gamma0Units`) lies in $H$, and `GammaHUpper M H ℓ` is the subgroup of $\Gamma_H(M)$ cut out by the condition that the upper-right entry vanishes in $\mathbb{Z}/\ell$; with the local instance making the coset space finite, this subgroup has finite index. Let $V$ be an additive commutative group, $\iota$ a finite type, and $e$ a bijection from $\iota$ to the space of right cosets $\mathrm{Quotient}(\mathrm{rightRel}\,$`GammaHUpper M H ℓ`$)$. Let $F : \mathrm{Additive}\,\Gamma_H(M) \to_+ V$, i.e. a homomorphism $\Gamma_H(M) \to V$, and let $\gamma \in \Gamma_H(M)$. The assertion is that the value of `heckeT M H ℓ V F` — the image of $F$ under the group-theoretic transfer of the pullback of $F$ along the monoid homomorphism `conjL`, which sends $\begin{pmatrix} a & b \\ c & d\end{pmatrix}$ with $\ell \mid b$ to $\begin{pmatrix} a & b/\ell \\ c\ell & d\end{pmatrix}$ — at $\gamma$ equals $\sum_{i : \iota} F\big(\mathrm{conjL}(\mathrm{slip}(e\,i, \gamma))\big)$, where $\mathrm{slip}(q,\gamma) = r_q\,\gamma\,r_{q\gamma}^{-1}$ is formed from the chosen representatives $r$ of the right cosets $q$ and $q\gamma$.
--
--   This is the concrete cocycle-level formula for the Hecke operator $T_\ell$ on $H^1(\Gamma_H(M), V) = \mathrm{Hom}(\Gamma_H(M), V)$ defined via transfer: its value on $\gamma$ is a sum of $F$ over the coset-by-coset "slip" elements, twisted by conjugation back into $\Gamma_H(M)$, indexed by an arbitrary finite indexing $e$ of the right cosets. It is used in the comparisons of $T_\ell$ with degeneracy and diamond operators and in the identification of eigenvalues with $q$-expansion coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_heckeT_apply_eq_sumEquiv.lean

import Definitions.Def_CohCarrier_Lower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem CohCarrier.heckeT_apply_eq_sumEquiv (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    {V : Type} [AddCommGroup V] {ι : Type*} [Fintype ι]
    (e : ι ≃ Quotient (QuotientGroup.rightRel (GammaHUpper M H ℓ)))
    (F : Additive ↥(GammaH M H) →+ V) (γ : ↥(GammaH M H)) :
    heckeT M H ℓ V F (Additive.ofMul γ)
      = ∑ i : ι, F (Additive.ofMul (conjL M H ℓ (slip (GammaHUpper M H ℓ) (e i) γ))) := by sorry
