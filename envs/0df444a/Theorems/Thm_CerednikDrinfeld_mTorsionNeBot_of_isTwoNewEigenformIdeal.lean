-- Prove2me | Theorems.Thm_CerednikDrinfeld_mTorsionNeBot_of_isTwoNewEigenformIdeal
-- name    : CerednikDrinfeld.mTorsionNeBot_of_isTwoNewEigenformIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/3d5dbf96-2b37-5c9d-84f1-067b331c148d
-- title:
--   Nonvanishing 𝔪-torsion for doubly-new eigenform ideals
-- statement:
--   Let $M$, $q$, $q'$ and $p$ be natural numbers and let $J$ be an abelian group equipped with a module structure over `HeckeAlg`, the polynomial ring $\mathbb{Z}[T_\ell : \ell \text{ prime}]$ in indeterminates indexed by the primes. Assume `EigenformSupportAt M p J`: for every ideal $\mathfrak{n}$ of `HeckeAlg` satisfying `IsEigenformIdeal M` — that is, arising as the kernel of the evaluation homomorphism `MvPolynomial.aeval` at the system $\ell \mapsto \varphi(a_\ell(f))$ for some weight-two cusp form $f$ on $\Gamma_0(M)$ which is a normalised eigenform (its $q$-expansion coefficients satisfy $a_1 = 1$, multiplicativity at coprime indices, and the recursions $a_{p^{r+2}} = a_p a_{p^{r+1}} - p\,a_{p^r}$ for primes $p \nmid M$ and $a_{p^{r+2}} = a_p a_{p^{r+1}}$ for $p \mid M$), some finite field $k$, some subring $\mathcal{O} \subseteq \mathbb{C}$ containing all the $a_\ell(f)$ for $\ell$ prime, and some ring homomorphism $\varphi : \mathcal{O} \to k$ — and which contains the image of $p$ in `HeckeAlg`, the submodule of $\mathfrak{n}$-torsion of $J$ is nonzero. Let $\mathfrak{m}$ be an ideal of `HeckeAlg` satisfying `IsTwoNewEigenformIdeal M q q'`, namely admitting such a presentation with a normalised eigenform $f$ of weight two on $\Gamma_0(M)$ whose coefficients additionally satisfy $a_q(f)^2 = 1$ and $a_{q'}(f)^2 = 1$, and suppose the image of $p$ lies in $\mathfrak{m}$. Then the $\mathfrak{m}$-torsion submodule `Submodule.torsionBySet HeckeAlg J 𝔪` of $J$ is not the zero submodule.
--
--   This is the statement that a Hecke module with eigenform support at level $M$ and residue characteristic $p$ has nonzero $\mathfrak{m}$-torsion at an ideal attached to a weight-two eigenform on $\Gamma_0(M)$ that is new at both $q$ and $q'$; in the Čerednik–Drinfeld part of the argument such nonvanishing plays the role of positivity of the Boston–Lenstra–Ribet multiplicity. It feeds the construction of lower-level torsion used in [`WeierstrassCurve.exists_hasLowerLevelTorsion_jZero_of_twoNewEigenformCongruence_sqf_five`](thm.html#WeierstrassCurve.exists_hasLowerLevelTorsion_jZero_of_twoNewEigenformCongruence_sqf_five).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_mTorsionNeBot_of_isTwoNewEigenformIdeal.lean

import Definitions.Def_ModularCurve_TwoNewEigenformIdeal
import Definitions.Def_ModularCurve_EigenformIdeal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem CerednikDrinfeld.mTorsionNeBot_of_isTwoNewEigenformIdeal {M q q' : ℕ} (p : ℕ)
    (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
    (hES : EigenformSupportAt M p J) {𝔪 : Ideal HeckeAlg}
    (h𝔪 : IsTwoNewEigenformIdeal M q q' 𝔪) (hp : (p : HeckeAlg) ∈ 𝔪) :
    MTorsionNeBot HeckeAlg J 𝔪 := by sorry
