-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_rightConv_diagOne_mul_mul_unipotentGL2_le_of_le_ideleNorm
-- name    : AutomorphicForm.exists_norm_rightConv_diagOne_mul_mul_unipotentGL2_le_of_le_ideleNorm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/2dae62bc-2bd8-599b-9cfd-dd607e80cd55
-- title:
--   Decay of a convolved cusp form along diag(a,1)
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite set of elements of $\mathrm{GL}_2(\mathbb A_F)$. Write $D=\bigcup_{x\in T}\{g x : g\in\mathfrak S\}$, where $\mathfrak S=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place $w$ has `localHeight` at least $c$ and `xWindowSq` at most $u^2$, and with `archDetNorm` $w\,g\in[d_1,d_2]$ for all $w$. Assume `CoversModCentre F D`, i.e. every $g\in\mathrm{GL}_2(\mathbb A_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\cdot(\text{central scalar } z)\in D$. Let the carrier data be `productionPinsOf F D` with level subgroups $N\mapsto$ `levelOne` $\sqcap$ $\ker(\mathrm{glArch})$, Hecke generators `heckeGen`, the Borel structure and adelic Haar measure on $\mathrm{GL}_2(\mathbb A_F)$, full central group $Z=\top$, and $\nu$ the adelic additive Haar measure conditioned on `adelicBox F`; let $\xi:Z\to\mathbb C^\times$ be a character. Let $\varphi:\mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ be continuous and satisfy `IsCuspAutomorphicFnAt` for these data and $\xi$ (that is, `IsAutomorphicFnAt` together with cuspidality of $\varphi$ along `unipotentGL2` with respect to $\nu$), and let $f$ be a factorizable test function, i.e. $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with archimedean and finite test factors. Then for every compact $C\subseteq\mathrm{GL}_2(\mathbb A_F)$ and every $k\in\mathbb N$ there exist reals $A_0$, $C_{\mathrm{st}}$ and $M\in\mathbb N$ such that for all idele units $a$, all $g\in C$ and all adeles $x$ with $\|a\|\ge A_0$, where $\|\cdot\|$ is `ideleNorm` (the value of the distributive Haar character), the right convolution $\varphi*f$, defined by $(\varphi*f)(h)=\int\varphi(hy)f(y)\,dy$ against adelic Haar measure on $\mathrm{GL}_2(\mathbb A_F)$, satisfies $$\bigl\|(\varphi*f)(\operatorname{diag}(a,1)\,g\,n(x))\bigr\|\le C_{\mathrm{st}}\,\|a\|^{-k}\,\bigl(H(g\,n(x))^{-1}\bigr)^{M},$$ with $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $H=$ `adelicHeight` $=$ `archHeight` $\cdot$ `finHeight`.
--
--   This is the large-$\|a\|$ range of the decay of a smoothed cusp form along the split torus, uniform for right translates by a compact set and with the loss in the unipotent variable measured by the adelic height of the right factor $g\,n(x)$. It feeds the two-sided torus estimate [`AutomorphicForm.exists_norm_unipotentAverage_rightConv_diagOne_mul_le_min_ideleNorm_pow`](thm.html#AutomorphicForm.exists_norm_unipotentAverage_rightConv_diagOne_mul_le_min_ideleNorm_pow), and is proved from the corresponding bounds on determinant-norm windows together with the scaling identity $H(\operatorname{diag}(a,1)h)=\|a\|\,H(h)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_rightConv_diagOne_mul_mul_unipotentGL2_le_of_le_ideleNorm.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal NumberField.AdelicHeight

theorem AutomorphicForm.exists_norm_rightConv_diagOne_mul_mul_unipotentGL2_le_of_le_ideleNorm
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (k : ℕ) :
    ∃ A₀ Cst : ℝ, ∃ M : ℕ, ∀ (a : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) (x : AdeleRing (𝓞 F) F),
      g ∈ C → A₀ ≤ ideleNorm F a →
        ‖rightConv F φ f (diagOne a * g * unipotentGL2 x)‖ ≤
          Cst * (ideleNorm F a)⁻¹ ^ k * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M := by sorry
