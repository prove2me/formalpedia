-- Prove2me | Theorems.Thm_CuspForm_qCoeff_one_ne_zero_and_isEigenformWith_smul_of_hasNebentypus_of_qCoeff_hecke_eigen_forall
-- name    : CuspForm.qCoeff_one_ne_zero_and_isEigenformWith_smul_of_hasNebentypus_of_qCoeff_hecke_eigen_forall
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/0e54b99c-399d-552c-ba12-38862f39baab
-- title:
--   Normalisation of a Hecke eigenform with nebentypus
-- statement:
--   Let $M \ge 1$, let $k \in \mathbb{Z}$, let $\varepsilon$ be a Dirichlet character modulo $M$ with values in $\mathbb{C}$, and let $g$ be a non-zero cusp form of weight $k$ for $\Gamma_1(M)$. Write $a_n(f) =$ [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19) for the $n$-th coefficient of the $q$-expansion of period $1$. Assume that $g$ has nebentypus $\varepsilon$, i.e. $g(\gamma\tau) = \varepsilon(\gamma_{11})\,(\gamma_{10}\tau + \gamma_{11})^{k} g(\tau)$ for all $\gamma \in \Gamma_0(M)$ and all $\tau$ in the upper half-plane, and let $b : \mathbb{N} \to \mathbb{C}$ be such that, for every prime $p \nmid M$ and every $n \ge 0$, $a_{pn}(g) + \varepsilon(p)\,p^{k-1}\,[p \mid n]\,a_{n/p}(g) = b_p\,a_n(g)$, and for every prime $q \mid M$ and every $n \ge 0$, $a_{qn}(g) = b_q\,a_n(g)$. The conclusion is threefold: $a_1(g) \neq 0$; the cusp form $h = a_1(g)^{-1}\, g$ satisfies [`CuspForm.IsEigenformWith`](def/CuspForm_PrimitiveFormGamma1.html#L19) for $\varepsilon$, that is $a_1(h) = 1$, $a_{pn}(h) + \varepsilon(p)\,p^{k-1}\,[p \mid n]\,a_{n/p}(h) = a_p(h)\,a_n(h)$ for all primes $p \nmid M$ and all $n$, $a_{\ell n}(h) = a_\ell(h)\,a_n(h)$ for all primes $\ell \mid M$ and all $n$, and $h$ again has nebentypus $\varepsilon$; and $a_p(h) = b_p$ for every prime $p$.
--
--   This is the standard normalisation step for a simultaneous Hecke eigenform with nebentypus: an eigenvector for all $T_p$ ($p \nmid M$) and all $U_q$ ($q \mid M$), expressed through its Fourier coefficients, has non-vanishing first coefficient and becomes, after rescaling, a normalised eigenform whose $p$-th coefficient is the corresponding eigenvalue. It is used to convert the eigenvector data produced from the Eichler–Shimura description of cuspidal cohomology into the normalised-eigenform datum on which the subsequent modularity arguments operate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_qCoeff_one_ne_zero_and_isEigenformWith_smul_of_hasNebentypus_of_qCoeff_hecke_eigen_forall.lean

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.qCoeff_one_ne_zero_and_isEigenformWith_smul_of_hasNebentypus_of_qCoeff_hecke_eigen_forall
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M)
    (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hg0 : g ≠ 0) (hε : CuspForm.HasNebentypus ε g)
    (b : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
      ModularFormClass.qCoeff g (p * n) +
          ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
        b p * ModularFormClass.qCoeff g n)
    (hU : ∀ q : ℕ, q.Prime → q ∣ M → ∀ n : ℕ,
      ModularFormClass.qCoeff g (q * n) = b q * ModularFormClass.qCoeff g n) :
    ModularFormClass.qCoeff g 1 ≠ 0 ∧
      CuspForm.IsEigenformWith ε ((ModularFormClass.qCoeff g 1)⁻¹ • g) ∧
      ∀ p : ℕ, p.Prime →
        ModularFormClass.qCoeff ((ModularFormClass.qCoeff g 1)⁻¹ • g) p = b p := by sorry
