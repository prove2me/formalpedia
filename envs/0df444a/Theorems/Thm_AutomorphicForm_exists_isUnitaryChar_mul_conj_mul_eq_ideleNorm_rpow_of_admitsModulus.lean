-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isUnitaryChar_mul_conj_mul_eq_ideleNorm_rpow_of_admitsModulus
-- name    : AutomorphicForm.exists_isUnitaryChar_mul_conj_mul_eq_ideleNorm_rpow_of_admitsModulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/06485e01-c554-5412-80f2-6f0654a5f6d8
-- title:
--   A compensating unitary idele class character, with local triviality
-- statement:
--   Let $K$ be a number field, let $\omega_1,\omega_2$ be group homomorphisms from the ideles $(\mathbb A_K)^\times$ to $\mathbb C^\times$, and let $w\in\mathbb R$. Assume $\lVert\omega_i(z)\rVert=(\mathrm{ideleNorm}\,z)^w$ for all ideles $z$ and $i=1,2$, where `ideleNorm` is the value at $z$ of the distributive Haar character of $\mathbb A_K$ viewed as a real number; assume each $z\mapsto\omega_i(z)$ is continuous as a $\mathbb C$-valued function; assume each $\omega_i$ is an idele class character, i.e. kills all principal ideles $\mathrm{im}(K^\times\to(\mathbb A_K)^\times)$. Let $N_1,N_2$ be nonzero ideals of $\mathcal O_K$ such that $\omega_i$ admits $N_i$ as a modulus: $\omega_i(u)=1$ whenever the archimedean component of $u$ is $1$ and, at every finite place $v$, $\lvert u_v\rvert_v=1$ and $\lvert u_v-1\rvert_v\le \exp(-\mathrm{ord}_v N_i)$, with $\mathrm{ord}_v N_i$ the multiplicity of $v$ in the factorisation of $N_i$. Then there is a homomorphism $\nu:(\mathbb A_K)^\times\to\mathbb C^\times$ which is unitary ($\lVert\nu(x)\rVert=1$ for all $x$), trivial on principal ideles, continuous as a $\mathbb C$-valued function, satisfies $\omega_1(z)\,\overline{\omega_2(z)}\,\nu(z)=(\mathrm{ideleNorm}\,z)^{2w}$ for all $z$, and is locally trivial as follows: for every finite place $v$ and every $n\ge 1$ with $\mathrm{ord}_v N_1\le n$ and $\mathrm{ord}_v N_2\le n$, the local character $\nu_v$ (that is, $\nu$ evaluated on the idele with component $t$ at $v$ and $1$ elsewhere) is trivial on all $t\in(K_v)^\times$ with $\lvert t-1\rvert_v\le q_v^{-n}$; and for every finite $v$ with $v\nmid N_1$, $v\nmid N_2$, the character $\nu_v$ is trivial on all $t$ with $t$ and $t^{-1}$ both in the valuation ring, i.e. $\nu$ is unramified at $v$.
--
--   This produces the auxiliary inducing character used to build the Eisenstein series attached to a pair of idele class characters in the Rankin–Selberg integral, together with the bounds on its ramification coming from the moduli of the two given characters. It is cited in the construction of test data for which the relevant Rankin–Selberg $s$-part integral is analytic on a neighbourhood and nonvanishing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isUnitaryChar_mul_conj_mul_eq_ideleNorm_rpow_of_admitsModulus.lean

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_NumberField_IdeleBox
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter
open scoped NNReal

theorem AutomorphicForm.exists_isUnitaryChar_mul_conj_mul_eq_ideleNorm_rpow_of_admitsModulus
    (K : Type) [Field K] [NumberField K]
    (ω₁ ω₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
    (hω₁ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ω₁ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
    (hω₂ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ω₂ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
    (hω₁c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ω₁ z : ℂˣ) : ℂ))
    (hω₂c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ω₂ z : ℂˣ) : ℂ))
    (hω₁F : IsIdeleClassChar (𝓞 K) K ω₁) (hω₂F : IsIdeleClassChar (𝓞 K) K ω₂)
    (N₁ N₂ : Ideal (𝓞 K)) (hN₁ : N₁ ≠ ⊥) (hN₂ : N₂ ≠ ⊥)
    (hmod₁ : HeckeCharacter.AdmitsModulus K ω₁ N₁) (hmod₂ : HeckeCharacter.AdmitsModulus K ω₂ N₂) :
    ∃ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      IsUnitaryChar (𝓞 K) K ν ∧ IsIdeleClassChar (𝓞 K) K ν ∧
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((ω₁ z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ω₂ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ)) ∧
      (∀ (v : HeightOneSpectrum (𝓞 K)) (n : ℕ), HeckeCharacter.idealMultiplicity K v N₁ ≤ n →
        HeckeCharacter.idealMultiplicity K v N₂ ≤ n → 1 ≤ n →
        ∀ t : (v.adicCompletion K)ˣ, Valued.v ((t : v.adicCompletion K) - 1) ≤
            ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
          NumberField.TateGlobal.localChar ν v t = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ N₁ → ¬ v.asIdeal ∣ N₂ →
        NumberField.TateGlobal.IsUnramifiedCharAt ν v) := by sorry
