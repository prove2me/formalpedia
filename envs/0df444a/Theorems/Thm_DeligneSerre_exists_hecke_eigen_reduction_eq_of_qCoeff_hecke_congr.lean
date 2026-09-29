-- Prove2me | Theorems.Thm_DeligneSerre_exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr
-- name    : DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/103004f0-41fd-5e42-9832-1b9ea3521695
-- title:
--   Deligne–Serre lifting lemma for forms of type (w,ε)
-- statement:
--   Let $N\ge 1$ and $w$ be natural numbers, let $\varepsilon$ be a Dirichlet character modulo $N$ with values in $\mathbb{C}$, and let $h$ be a cusp form of weight $w$ on $\Gamma_1(N)$ having nebentypus $\varepsilon$, meaning that $h(\gamma\tau)=\varepsilon(\gamma_{11}\bmod N)\,(\gamma_{10}\tau+\gamma_{11})^{w}h(\tau)$ for every $\gamma\in\Gamma_0(N)$ and every $\tau$ in the upper half-plane. Write $a_n(f)$ for the $n$-th coefficient [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19) of the $q$-expansion of period $1$ at $\infty$. Let $R$ be a $\mathbb{Z}$-subalgebra of $\mathbb{C}$ containing all $a_n(h)$ and all values of $\varepsilon$, let $\kappa$ be a finite field and $\varphi\colon R\to\kappa$ a ring homomorphism with $\varphi(a_n(h))\neq 0$ for at least one $n$, and let $\alpha\colon\mathbb{N}\to R$. Assume that for every prime $p$ with $p\nmid N$ and $p\neq 0$ in $\kappa$ and every $n$ there is $r\in R$ whose image in $\mathbb{C}$ equals $a_{pn}(h)+\varepsilon(p)\,p^{\,w-1}\,[p\mid n]\,a_{n/p}(h)$ (the exponent $w-1$ being truncated subtraction of naturals) and with $\varphi(r)=\varphi(\alpha_p)\varphi(a_n(h))$. Then there exist a nonzero cusp form $g$ of weight $w$ on $\Gamma_1(N)$ with nebentypus $\varepsilon$ and a function $b\colon\mathbb{N}\to\mathbb{C}$ such that $a_{pn}(g)+\varepsilon(p)\,p^{\,w-1}\,[p\mid n]\,a_{n/p}(g)=b_p\,a_n(g)$ for every prime $p\nmid N$ and every $n$, together with a $\mathbb{Z}$-subalgebra $R'\subseteq\mathbb{C}$ and a ring homomorphism $\varphi'\colon R'\to\kappa$ such that every value $\varepsilon(x)$ lies in $R'$ with $\varphi'(\varepsilon(x))=\varphi(\varepsilon(x))$, and such that for every prime $p\nmid N$ with $p\neq 0$ in $\kappa$ one has $b_p\in R'$ and $\varphi'(b_p)=\varphi(\alpha_p)$.
--
--   This is the Deligne–Serre lifting lemma in the form used for cusp forms of type $(w,\varepsilon)$ on $\Gamma_1(N)$: a form which is an eigenvector of the Hecke operators $T_p$, $p\nmid N\ell$, only modulo $\ker\varphi$ is replaced by a genuine eigenform of the same weight, level and nebentypus whose eigenvalues reduce to the given residual ones. It is used by [`DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen`](thm.html#DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen) in the passage from weight one to weight two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr.lean

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr
    (N : ℕ) [NeZero N] (w : ℕ) (ε : DirichletCharacter ℂ N)
    (h : CuspForm (Gamma1 N) w) (hεh : CuspForm.HasNebentypus ε h)
    (R : Subalgebra ℤ ℂ) (hR : ∀ n : ℕ, ModularFormClass.qCoeff h n ∈ R)
    (hε : ∀ x : ZMod N, ε x ∈ R)
    (κ : Type) [Field κ] [Finite κ] (φ : R →+* κ)
    (hne : ∃ n : ℕ, φ ⟨ModularFormClass.qCoeff h n, hR n⟩ ≠ 0)
    (α : ℕ → R)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → (p : κ) ≠ 0 → ∀ n : ℕ, ∃ r : R,
        (r : ℂ) = ModularFormClass.qCoeff h (p * n) +
            ε (p : ZMod N) * (p : ℂ) ^ (w - 1) *
              (if p ∣ n then ModularFormClass.qCoeff h (n / p) else 0) ∧
        φ r = φ (α p) * φ ⟨ModularFormClass.qCoeff h n, hR n⟩) :
    ∃ (g : CuspForm (Gamma1 N) w) (b : ℕ → ℂ), g ≠ 0 ∧ CuspForm.HasNebentypus ε g ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff g (p * n) +
            ε (p : ZMod N) * (p : ℂ) ^ (w - 1) *
              (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
          b p * ModularFormClass.qCoeff g n) ∧
      ∃ (R' : Subalgebra ℤ ℂ) (φ' : R' →+* κ),
        (∀ x : ZMod N, ∃ hx : ε x ∈ R', φ' ⟨ε x, hx⟩ = φ ⟨ε x, hε x⟩) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → (p : κ) ≠ 0 →
          ∃ hb : b p ∈ R', φ' ⟨b p, hb⟩ = φ (α p) := by sorry
