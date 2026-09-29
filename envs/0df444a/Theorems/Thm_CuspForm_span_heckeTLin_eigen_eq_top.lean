-- Prove2me | Theorems.Thm_CuspForm_span_heckeTLin_eigen_eq_top
-- name    : CuspForm.span_heckeTLin_eigen_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/72ce3f3f-a2bd-54b9-8ac2-5e0afdca5605
-- title:
--   Good Hecke eigenvectors span S₂(Γ₀(M))
-- statement:
--   Let $M$ be a natural number which is nonzero (the typeclass assumption `NeZero M`). Consider the complex vector space $S_2(\Gamma_0(M))$ of cusp forms of weight $2$ for the congruence subgroup $\Gamma_0(M)$, and let $E \subseteq S_2(\Gamma_0(M))$ be the set of those $v$ with the property that for every natural number $\ell$ which is prime and does not divide $M$ there exists a scalar $c \in \mathbb{C}$ with $T_\ell v = c\,v$, where $T_\ell$ denotes the $\mathbb{C}$-linear endomorphism [`CuspForm.heckeTLin`](def/ModularForm_HeckeOperatorForms.html#L69) of $S_2(\Gamma_0(M))$ attached to such an $\ell$; on underlying functions on the upper half-plane this endomorphism sends $f$ to $\mathrm{heckeU}\,2\,\ell\,f + f \mid_2 \mathrm{heckeDiagMatrix}\,\ell$, the sum of the averaging operator over the upper-triangular representatives and the weight-$2$ slash by the diagonal matrix at $\ell$. The assertion is that the $\mathbb{C}$-linear span of $E$ is the whole space $S_2(\Gamma_0(M))$. Note that $E$ consists of simultaneous eigenvectors for the Hecke operators at the primes away from $M$ only, no condition being imposed at primes dividing $M$; the eigenvalue $c$ may depend on $\ell$, the zero form lies in $E$ vacuously, and only spanning, not linear independence or multiplicity one, is claimed.
--
--   This is the classical spectral statement that the weight-two cusp forms of level $M$ are spanned by simultaneous eigenvectors of the Hecke operators at the good primes, obtained from selfadjointness of those operators for the Petersson product. It underlies the newform theory used later, being cited in the comparison results [`CuspForm.IsNewform.eq_of_forall_qCoeff_eq`](thm.html#CuspForm.IsNewform.eq_of_forall_qCoeff_eq) and [`CuspForm.IsNewform.level_eq_of_forall_prime_not_dvd_qCoeff_eq`](thm.html#CuspForm.IsNewform.level_eq_of_forall_prime_not_dvd_qCoeff_eq) and in [`CuspForm.span_rescaleLin_isNewform_eq_top`](thm.html#CuspForm.span_rescaleLin_isNewform_eq_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean

import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.span_heckeTLin_eigen_eq_top (M : ℕ) [NeZero M] :
    Submodule.span ℂ {v : CuspForm (CongruenceSubgroup.Gamma0 M) 2 |
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∃ c : ℂ,
        CuspForm.heckeTLin 2 hℓ hℓM v = c • v} = ⊤ := by sorry
