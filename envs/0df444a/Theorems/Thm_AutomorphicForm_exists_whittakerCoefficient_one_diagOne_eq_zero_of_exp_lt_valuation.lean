-- Prove2me | Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation
-- name    : AutomorphicForm.exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/a2510a76-a0b2-5aa2-870e-bd98a8b4f4cd
-- title:
--   Support of the first Whittaker coefficient on the torus diag(b,1)
-- statement:
--   Let $F$ be a number field, let $D$ be a subset of $\mathrm{GL}_2$ of the adele ring of $F$, let $U$ assign to each ideal of $\mathcal O_F$ a subgroup of that group, and let $\mathrm{gen}$ assign to each finite place an element of it. Let $\psi$ be an additive character of $\mathbb A_F$ with values in $\mathbb C$ which is global in the sense of `IsGlobalAddChar`, i.e. trivial on the image of $F$, continuous, and not identically $1$. Let $\varphi\colon \mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ satisfy $\varphi(n(\beta)g)=\varphi(g)$ for all $\beta\in F$ and all $g$, where $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and assume $\varphi$ is $K_f$-smooth, i.e. a smooth vector for right translation by the kernel of the archimedean projection `glArch` on $\mathrm{GL}_2(\mathbb A_F)$. Then there is a function $c$ from the finite places of $F$ to $\mathbb Z$, vanishing outside some finite set $S$ of places, such that for every unit $b$ of $\mathbb A_F$: if some finite place $v$ satisfies $\exp(c_v)<\lvert b_v\rvert_v$, where $b_v$ is the component at $v$ of the finite-adelic part of $b$ and the valuation takes values in $\mathbb Z$ written multiplicatively via `WithZero.exp`, then $$\int \varphi(n(x)\,\mathrm{diag}(b,1))\,\psi(-x)\,d\nu(x)=0,$$ the Whittaker coefficient at $\alpha=1$ and $g=\mathrm{diag}(b,1)$ taken with respect to the measure component of `productionPinsOf F D U gen (adelicBox F)`, namely adelic additive Haar measure conditioned on the box whose archimedean part is a fundamental domain for the Minkowski lattice and whose finite part consists of the everywhere-integral finite adeles. The value of the coefficient involves $D$, $U$ and $\mathrm{gen}$ only as inert components of that record.
--
--   This is the finite-place support (conductor) bound for the first Whittaker coefficient of a $K_f$-smooth, unipotently invariant function restricted to the torus $b\mapsto \mathrm{diag}(b,1)$: the coefficient vanishes once some finite component of $b$ is too large. It is used to control the zeta integrands built from Whittaker coefficients in the Rankin–Selberg analyticity and integrability statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation.lean

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm

theorem AutomorphicForm.exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = φ g)
    (hsm : IsKfSmooth F φ) :
    ∃ c : HeightOneSpectrum (𝓞 F) → ℤ,
      (∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, c v = 0) ∧
      ∀ b : (AdeleRing (𝓞 F) F)ˣ,
        (∃ v : HeightOneSpectrum (𝓞 F),
          WithZero.exp (c v) < Valued.v (((b : AdeleRing (𝓞 F) F).2) v)) →
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 (diagOne b) = 0 := by sorry
