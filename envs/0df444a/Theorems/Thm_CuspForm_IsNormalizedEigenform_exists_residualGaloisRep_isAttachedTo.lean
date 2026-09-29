-- Prove2me | Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_residualGaloisRep_isAttachedTo
-- name    : CuspForm.IsNormalizedEigenform.exists_residualGaloisRep_isAttachedTo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/c076fbb2-eb2c-5d4c-a5d3-640164f63f27
-- title:
--   Residual Galois representation of a weight-two eigenform
-- statement:
--   Let $N$ be a natural number and let $g$ be a cusp form of weight $2$ for $\Gamma_0(N)$ which is a normalised eigenform in the sense of the project's structure: the first coefficient of its $q$-expansion is $1$, the coefficients are multiplicative on coprime indices, and at every prime $q$ they satisfy $a_{q^{r+2}} = a_q a_{q^{r+1}} - q\,a_{q^{r}}$ if $q \nmid N$ and $a_{q^{r+2}} = a_q a_{q^{r+1}}$ if $q \mid N$. Let $p$ be a prime, $k$ a field of characteristic $p$, and $\varphi$ a ring homomorphism from the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ (the algebraic integers) to $k$. Then there exists a residual Galois representation $\rho$ over $k$, that is, a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathrm{End}_k(V)$ which is trivial on the automorphisms fixing some finite-dimensional intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ pointwise, with the following two properties. First, $\rho$ is attached to $g$ along $\varphi$: for every prime $\ell$ with $\ell \nmid N$ and $\ell \neq 0$ in $k$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$, and every $\sigma$ in the decomposition subgroup of $A$ acting on the residue field of $A$ by $x \mapsto x^{\ell}$, there is an algebraic integer $a$ whose image in $\mathbb{C}$ is the $\ell$-th $q$-expansion coefficient of $g$ and such that the characteristic polynomial of $\rho(\sigma)$ equals $X^2 - \varphi(a)X + \ell$ in $k[X]$. Second, $\rho$ is unramified at every prime $\ell$ not dividing $Np$: for every valuation subring $A$ of $\overline{\mathbb{Q}}$ having $\ell$ as a non-unit, $\rho$ sends every element of the image of the inertia subgroup of $A$ over $\mathbb{Q}$ to the identity.
--
--   This is the existence half of the Eichler–Shimura–Deligne construction, in its residual form: the mod-$p$ two-dimensional representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ attached to a weight-two normalised eigenform on $\Gamma_0(N)$ through a homomorphism $\varphi$ from the algebraic integers to $k$, with the Eichler–Shimura relation recorded as a characteristic polynomial identity at Frobenius elements. It is the shared input to the level-lowering argument for the Frey curve and to the residual modularity statements used in the modularity-lifting step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNormalizedEigenform_exists_residualGaloisRep_isAttachedTo.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.IsNormalizedEigenform.exists_residualGaloisRep_isAttachedTo
    {N : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g.IsNormalizedEigenform)
    {p : ℕ} (hp : p.Prime) {k : Type} [Field k] [CharP k p]
    (φ : integralClosure ℤ ℂ →+* k) :
    ∃ ρ : ResidualGaloisRep k, ρ.IsAttachedTo g φ ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p → ρ.IsUnramifiedAt ℓ := by sorry
