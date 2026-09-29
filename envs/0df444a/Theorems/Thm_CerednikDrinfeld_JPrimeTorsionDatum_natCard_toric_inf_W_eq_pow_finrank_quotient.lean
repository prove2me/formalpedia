-- Prove2me | Theorems.Thm_CerednikDrinfeld_JPrimeTorsionDatum_natCard_toric_inf_W_eq_pow_finrank_quotient
-- name    : CerednikDrinfeld.JPrimeTorsionDatum.natCard_toric_inf_W_eq_pow_finrank_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/99bfba54-53e3-52ee-93df-eb39f94b6f71
-- title:
--   Counting the toric part of the 𝔪-torsion
-- statement:
--   Fix a prime $p$, finite types $E$ and $V$, a valuation subring $A$ of $\overline{\mathbb Q}$, and a datum `Dm : JPrimeTorsionDatum p E V A`, that is: degeneracy data $D$ on $E$, $V$ (two maps $a,b : E \to V$ and weights $E \to \mathbb N_{>0}$), Hecke data $H$ for $D$ (commuting matrices $T_\ell$ on $E$ and $T_\ell^{v}$ on $V$, compatible with both pushforwards outside a finite set of primes and always preserving the ribbon kernel $Z = \operatorname{ribbonKernel} D$, the intersection of the kernels of the two pushforwards on $E \to \mathbb Z$), a finite abelian group $T$ killed by $p$, a ring homomorphism from $\mathbb T =$ `HeckeAlg` $= \mathbb Z[X_\ell : \ell \text{ prime}]$ to $\operatorname{End}_{\mathbb Z}(T)$, a Galois action on $T$ commuting with it and trivial on some finite extension of $\mathbb Q$, a subgroup $\mathcal T =$ `Dm.toric` of $T$, an additive identification $\mathcal T \cong \operatorname{Hom}_{\mathbb Z}(Z, \mathbb Z/p)$, and a specialisation map from the inertia invariants of $T$ at $A$ to $\operatorname{ribbonComponentGroup} D$. Assume $\mathcal T$ is stable under the whole action of $\mathbb T$, and that for every prime $\ell$ the identification carries the action of $X_\ell$ on $\mathcal T$ to precomposition with `heckeKernelMap Dm.H ℓ`, the restriction to $Z$ of the linear map of the matrix $T_\ell$. Let $\mathfrak m$ be a maximal ideal of $\mathbb T$ containing the constant $p$, and let $Y$ be a $\mathbb T$-module together with an additive isomorphism $e_Y : Y \cong Z$ under which $X_\ell$ acts through `heckeKernelMap Dm.H ℓ` for every prime $\ell$. Then the cardinality of the intersection of $\mathcal T$ with the subgroup `Dm.W 𝔪` of $T$ attached to $\mathfrak m$ equals $\#(\mathbb T/\mathfrak m)$ raised to the power $\dim_{\mathbb T/\mathfrak m} Y/\mathfrak m Y$.
--
--   This is the character-group duality count for the toric part of the $p$-torsion at one place: the $\mathfrak m$-part of the toric subgroup is dual to the coinvariants $Y/\mathfrak m Y$ of the character lattice. It is applied at each of the two places in the dimension count for the two-place torsion datum, and is cited by the inequalities comparing the $\mathfrak m$-coinvariants of the old and ribbon lattices with the cardinality of the corresponding toric torsion groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_JPrimeTorsionDatum_natCard_toric_inf_W_eq_pow_finrank_quotient.lean

import Definitions.Def_CerednikDrinfeld_JPrimeTorsionDatum
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CerednikDrinfeld ModularCurve

theorem CerednikDrinfeld.JPrimeTorsionDatum.natCard_toric_inf_W_eq_pow_finrank_quotient
    {p : ℕ} [Fact p.Prime] {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    (Dm : JPrimeTorsionDatum p E V A)
    (htor : ∀ (x : HeckeAlg) (t : Dm.T), t ∈ Dm.toric → Dm.hecke x t ∈ Dm.toric)
    (hlaw : ∀ (ℓ : Nat.Primes) (t : Dm.T) (ht : t ∈ Dm.toric) (hℓt : Dm.hecke (heckeGen ℓ) t ∈ Dm.toric),
      Dm.toricEquiv ⟨Dm.hecke (heckeGen ℓ) t, hℓt⟩ = (Dm.toricEquiv ⟨t, ht⟩) ∘ₗ heckeKernelMap Dm.H ℓ)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp : (p : HeckeAlg) ∈ 𝔪)
    {Y : Type} [AddCommGroup Y] [Module HeckeAlg Y]
    (eY : Y ≃+ ↥(ribbonKernel Dm.D))
    (hY : ∀ (ℓ : Nat.Primes) (m : Y), eY (heckeGen ℓ • m) = heckeKernelMap Dm.H ℓ (eY m)) :
    Nat.card ↥(Dm.toric ⊓ Dm.W 𝔪) =
      Nat.card (HeckeAlg ⧸ 𝔪) ^ Module.finrank (HeckeAlg ⧸ 𝔪) (Y ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Y))) := by sorry
