-- Prove2me | Theorems.Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_isFundamentalDomain
-- name    : AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/7e7d567b-55e6-53d4-aa82-4b8cbfb9200d
-- title:
--   Boundedness of smoothed cusp forms on Siegel windows
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta$ be reals with $0<\beta$ and $\alpha<\beta$, and let $S\subseteq \mathrm{GL}_2(\mathbb{A}_F)$ be a fundamental domain for the image of $\mathrm{GL}_2(F)$ under `globalPoints` (the entrywise map induced by $F\hookrightarrow\mathbb{A}_F$) with respect to the adelic Haar measure `adelicGLHaar` restricted to the determinant slab $\{g: \mathrm{ideleNorm}_F(\det g)\in[\alpha,\beta]\}$, the idele norm being the distributive Haar character of $\mathbb{A}_F$. Let $U$ be an arbitrary family of subgroups indexed by ideals of $\mathcal{O}_F$, $gen$ an arbitrary family of adelic matrices indexed by the height-one spectrum, and form the carrier pins `productionPinsOf F S U gen (adelicBox F)`: Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, domain $S$, centre subgroup $\top$ in $\mathbb{A}_F^\times$, the data $U,gen$, and on $\mathbb{A}_F$ the Borel structure with the additive Haar measure conditioned on the box $\{x:x_\infty\in \mathrm{infiniteBox}\ F,\ x_{\mathrm{fin}}\ \text{integral}\}$. Let $\chi:\top\to\mathbb{C}^\times$ be a homomorphism and $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ continuous, satisfying `IsCuspAutomorphicFnAt` for these pins and $\chi$: that is, $\varphi$ satisfies the membership predicate `LsXiMemberAt` for the pins' measure, centre and domain (which splits into $\varphi$ being an `IsLsXiFunction` for $\top$ and $\chi$, and $\varphi\in L^2$ of the Haar measure restricted to $S$), and all constant terms of $\varphi$ along the unipotent matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ against the conditioned additive measure vanish. Let $f$ be a factorizable test function, i.e. $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ an `IsArchTestFactor` and $f_{\mathrm{fin}}$ an `IsFinTestFactor`. Then $\mathrm{rightConv}(\varphi,f)(g)=\int \varphi(gx)f(x)\,dx$ is bounded on Siegel windows: for all reals $c,u,d_1,d_2$ with $c>0$, $d_1>0$ and every finite set $T$ of adelic matrices there is $C$ with $\|(\varphi*f)(g)\|\le C$ for all $g$ in the union over $x\in T$ of the right translates by $x$ of the centre-cut Siegel set $\{g:\ g_{\mathrm{fin}}$ integral, all local heights $\ge c$, all $x$-window squares $\le u^2$, all archimedean determinant norms in $[d_1,d_2]\}$.
--
--   This is Godement's boundedness estimate for smoothings of cuspidal functions, here with the square-integrability hypothesis taken over a fundamental domain of a determinant slab. It feeds the construction of the bounded cuspidal realization: it is used to show that right convolutions of cuspidal automorphic functions by factorizable test functions lie in the isotypic cusp submodule intersected with the archimedean cut submodule.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_isFundamentalDomain.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm.WindowedSiegel

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_isFundamentalDomain
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (hβ : 0 < β) (hαβ : α < β) (S : Set (AdelicGL2 (𝓞 F) F))
    (hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (χ : (productionPinsOf F S U gen (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F (productionPinsOf F S U gen (adelicBox F)) χ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsFactorizableTestFn F f) :
    IsBoundedOnSiegelWindows F (rightConv F φ f) := by sorry
