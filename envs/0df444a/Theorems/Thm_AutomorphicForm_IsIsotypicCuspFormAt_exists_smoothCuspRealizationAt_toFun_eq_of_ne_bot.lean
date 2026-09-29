-- Prove2me | Theorems.Thm_AutomorphicForm_IsIsotypicCuspFormAt_exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot
-- name    : AutomorphicForm.IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/e17e2b72-cd70-5a76-881a-7548087d47fd
-- title:
--   Isotypic cusp forms as smooth-cusp realizations at level N
-- statement:
--   Let $F$ be a number field, let $\mathrm{pins} : \mathrm{CarrierPins}\,F$ be a bundle of carrier data on $\mathrm{GL}_2(\mathbb A_F)$ (a measurable space and measure on $\mathrm{GL}_2(\mathbb A_F)$, a fundamental-domain set $D$, a centre subgroup $Z \le \mathbb A_F^\times$, level subgroups $U(\mathfrak m)$ indexed by ideals of $\mathcal O_F$, Hecke generators $\mathrm{gen}(v)$ indexed by finite places, and a measurable space and measure on $\mathbb A_F$), let $\xi : Z \to \mathbb C^\times$ be a homomorphism, let $N$ be a nonzero ideal of $\mathcal O_F$, let $S$ be a finite set of height-one primes of $\mathcal O_F$, let $\Psi = (\mathrm{level}, a, b)$ be a complex Hecke eigensystem for $F$, and let $\varphi : \mathrm{GL}_2(\mathbb A_F) \to \mathbb C$ satisfy $\mathrm{IsIsotypicCuspFormAt}$ for $(\mathrm{pins}, \xi, N, S, \Psi)$, i.e.\ $\varphi$ is cuspidal automorphic at $\mathrm{pins}$ with central character $\xi$ and $K_f$-smooth, is continuous, satisfies $\varphi(gu) = \varphi(g)$ for all $u \in U(N)$, and for every $v \notin S$ admits a coset system $(r_i)_{i < \mathrm N v + 1}$ for $U(N)\,\mathrm{gen}(v)\,U(N)$ with Hecke coset sum equal to $a_v\varphi$, and satisfies $\varphi(\mathrm{centralScalar}(\det \mathrm{gen}(v))\,g) = (\mathrm N v)^{-1} b_v\,\varphi(g)$ for all $g$. Assume $\varphi \neq 0$. Then there exist a Hecke eigensystem $\Psi'$ and a term $R$ of $\mathrm{SmoothCuspRealizationAt}\,F\,\mathrm{pins}\,\Psi'.\mathrm{toRawCentral}$ with $\Psi'.\mathrm{level} = N$, $\Psi'.a = \Psi.a$ and $\Psi'.b = \Psi.b$ pointwise, $R.\mathrm{toFun} = \varphi$, $R.\mathrm{centralChar} = \xi$ and $R.\mathrm{exceptionalSet} = S$.
--
--   This is the passage from the predicate form of membership in an isotypic cuspidal space at a given level to the bundled datum of a smooth-cusp realization: the clauses of $\mathrm{IsIsotypicCuspFormAt}$ read only the tables $a$ and $b$ of the eigensystem, so they become the fields of a realization of the eigensystem re-levelled at $N$ and rescaled by $b_v \mapsto (\mathrm N v)^{-1} b_v$. It is used downstream in the analysis of archimedean constituents of such realizations, where the bundled form is the convenient input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsIsotypicCuspFormAt_exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (Ψ : HeckeEigensystem F ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : IsIsotypicCuspFormAt F pins ξ N S Ψ φ) (h0 : φ ≠ 0) :
    ∃ (Ψ' : HeckeEigensystem F ℂ) (R : SmoothCuspRealizationAt F pins Ψ'.toRawCentral),
      Ψ'.level = N ∧ (∀ v, Ψ'.a v = Ψ.a v) ∧ (∀ v, Ψ'.b v = Ψ.b v) ∧
        R.toFun = φ ∧ R.centralChar = ξ ∧ R.exceptionalSet = S := by sorry
