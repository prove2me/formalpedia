-- Prove2me | Theorems.Thm_FLT_LedgerRows_ledg5_no2_hcurve_continuous
-- name    : FLT.LedgerRows.ledg5_no2_hcurve_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/439b9615-77b6-51d6-9d8b-a86bfcfdc5d9
-- title:
--   Continuous surjective mod-3 representation with prescribed Frobenius traces
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ with discriminant $\Delta(W) \neq 0$. Assume $W$ is a semistable model in the sense that for every prime $p$ with $p \mid \Delta(W)$ one has $p \nmid c_4(W)$, and assume the mod-$3$ irreducibility condition: the $3$-torsion subgroup $\mathrm{Tor}_3$ of the group of points of $W \otimes \mathbb{Q}$ over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` is nontrivial, and every Galois-stable $\mathbb{Z}/3$-submodule of it is $\bot$ or $\top$. Then there is a monoid homomorphism $\rho : \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(\mathbb{Z}/3)$, written with the Galois group as the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$, such that: $\rho$ is continuous; $\rho$ is surjective; $\det \rho(\sigma)$ equals $\sigma$'s value under the mod-$3$ cyclotomic character `modThreeCyclotomicChar` for every $\sigma$; and for every prime $\ell \neq 3$ with $\ell \nmid \Delta(W)$, every valuation subring $A \subseteq \overline{\mathbb{Q}}$ with $\ell$ a nonunit of $A$, and every $\sigma$ that is a Frobenius at $\ell$ for $A$ (that is, $\sigma$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acts on the residue field of $A$ by $x \mapsto x^{\ell}$), the trace of the matrix $\rho(\sigma)$ equals the image in $\mathbb{Z}/3$ of $a_\ell(W) = \ell + 1 - \#W(\mathbb{F}_\ell)$, the latter computed from the reduction of $W$ modulo $\ell$.
--
--   This is the curve-side statement of the mod-$3$ representation attached to the $3$-torsion of a semistable elliptic curve over $\mathbb{Q}$: surjectivity onto $\mathrm{GL}_2(\mathbb{F}_3)$ under the irreducibility hypothesis, determinant the cyclotomic character, and Frobenius traces given by the $a_\ell$. Note that $\rho$ is only asserted to exist as an abstract homomorphism with these properties, not identified with a specific representation on $E[3]$; it feeds the Langlands–Tunnell step and is used by [`FLT.No2BridgeWiring.weightOneNewformExists_levelAtThree_not_cube_dvd`](thm.html#FLT.No2BridgeWiring.weightOneNewformExists_levelAtThree_not_cube_dvd) and [`FLT.No2BridgeWiring.weightOneNewformExists_not_cube_dvd`](thm.html#FLT.No2BridgeWiring.weightOneNewformExists_not_cube_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FLT_LedgerRows_ledg5_no2_hcurve_continuous.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_GaloisRep_ModThreeCyclotomic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve
open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem FLT.LedgerRows.ledg5_no2_hcurve_continuous :
    ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → W.IsSemistableModel →
      W.ModRepIsIrreducible 3 →
      ∃ ρ : Γℚ →* GL (Fin 2) (ZMod 3),
        Continuous ρ ∧
        Function.Surjective ρ ∧
        (∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ) ∧
        ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ≠ 3 →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ →
              ((ρ σ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).trace
                = (W.apOfModel ℓ : ZMod 3) := by sorry
