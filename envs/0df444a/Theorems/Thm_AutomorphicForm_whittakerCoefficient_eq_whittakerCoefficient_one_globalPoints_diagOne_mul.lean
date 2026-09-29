-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul
-- name    : AutomorphicForm.whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/8e992663-0f19-58de-af19-1449adb3cd39
-- title:
--   Whittaker coefficients: W_α(g)=W₁(diag(α,1)g)
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A}_F$. Fix auxiliary data: a subset $D$ of $\mathrm{GL}_2(\mathbb{A}_F)$, a family $U$ of subgroups of $\mathrm{GL}_2(\mathbb{A}_F)$ indexed by the ideals of $\mathcal{O}_F$, and a family $\mathit{gen}$ of elements of $\mathrm{GL}_2(\mathbb{A}_F)$ indexed by the height one primes of $\mathcal{O}_F$; these are assembled, together with the adelic box $\{x : x_\infty \in \text{fundamental domain of the lattice } \mathcal{O}_F,\ x_v \in \mathcal{O}_v \text{ for all finite } v\}$, into the carrier data `productionPinsOf`, whose additive measure is the Haar measure of $\mathbb{A}_F$ conditioned on that box and whose group measure is the Haar measure of $\mathrm{GL}_2(\mathbb{A}_F)$. Let $\psi : \mathbb{A}_F \to \mathbb{C}$ be an additive character which is a global additive character, i.e. trivial on the image of $F$, continuous and nontrivial, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ satisfy $\varphi(\gamma g) = \varphi(g)$ for all $\gamma \in \mathrm{GL}_2(F)$ (acting through the entrywise map $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb{A}_F)$) and all $g$. Here the $\alpha$-th Whittaker coefficient at $g$ is $\int \varphi(n(x)g)\,\psi(-\alpha x)$ against that conditioned measure, $n(x)$ being the upper unipotent matrix with entry $x$. Then for every $\alpha \in F$ with $\alpha \neq 0$ and every $g \in \mathrm{GL}_2(\mathbb{A}_F)$, the $\alpha$-th coefficient at $g$ equals the first coefficient at $\mathrm{diag}(\alpha,1)\,g$, where $\mathrm{diag}(\alpha,1) \in \mathrm{GL}_2(F)$ is formed from the unit $\alpha$ and is mapped into $\mathrm{GL}_2(\mathbb{A}_F)$ entrywise.
--
--   This is the covariance of the Whittaker (Fourier) coefficients of a left $\mathrm{GL}_2(F)$-invariant function on $\mathrm{GL}_2(\mathbb{A}_F)$ under the rational diagonal torus elements $\mathrm{diag}(\alpha,1)$, which reduces all nonzero coefficients to the first one and so opens the Fourier–Whittaker expansion of an adelic automorphic form. It is used in the estimates on class sums and on the decay of forms with vanishing constant term.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (α : F) (hα : α ≠ 0) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (AdelicBox.adelicBox F)) ψ φ α g
      = whittakerCoefficient F (productionPinsOf F D U gen (AdelicBox.adelicBox F)) ψ φ 1
          (globalPoints (𝓞 F) F (AdelicLevel.diagOne (Units.mk0 α hα)) * g) := by sorry
