-- Prove2me | Theorems.Thm_AutomorphicForm_summable_norm_godementSection_adelicWeyl_unipotentGL2_mul_of_mem_schwartzBruhat2_of_half_lt_re
-- name    : AutomorphicForm.summable_norm_godementSection_adelicWeyl_unipotentGL2_mul_of_mem_schwartzBruhat2_of_half_lt_re
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/0f42e345-606e-535e-96c3-c03911fdb32a
-- title:
--   Godement's lemma: absolute convergence of the Bruhat series for Re s>1/2
-- statement:
--   Let $F$ be a number field, let the unit group $\mathbb{A}_F^\times$ of the adele ring carry a measurable structure which is the Borel structure of its topology, and let $\nu_0$ be a Haar measure on $\mathbb{A}_F^\times$; the matrix group $\mathrm{GL}_2(\mathbb{A}_F)$ is given its Borel structure. Let $\mu,\nu:\mathbb{A}_F^\times\to\mathbb{C}^\times$ be group homomorphisms, each trivial on the principal ideles $F^\times$ (so idele class characters), each unitary in the sense that $|\chi(x)|=1$ for all $x$, and each continuous as a $\mathbb{C}$-valued function. Let $\Phi:\mathbb{A}_F^2\to\mathbb{C}$ lie in `schwartzBruhat2 F`, the $\mathbb{C}$-span of the pure tensors $x\mapsto g(x_\infty)h(x_{\mathrm{fin}})$ with $g$ Schwartz on the two-fold mixed space of $F$ and $h$ locally constant of compact support on $(\widehat{\mathbb{A}}_F)^2$, and let $s\in\mathbb{C}$ satisfy $\operatorname{Re} s>1/2$. Then for every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ the family indexed by $\xi\in F$ of the absolute values $\bigl|f_s\bigl(w\,n(\xi)\,g\bigr)\bigr|$ is summable, where $w$ is the image in $\mathrm{GL}_2(\mathbb{A}_F)$ of the antidiagonal involution $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ over $F$, $n(\xi)=\begin{pmatrix}1&\xi\\0&1\end{pmatrix}$ is the image of $\xi$ under $F\to\mathbb{A}_F$, the product is taken in the order $w\cdot n(\xi)\cdot g$, and $$f_s(g)=\mu(\det g)\,\alpha(\det g)^{s+1/2}\int_{\mathbb{A}_F^\times}\Phi\bigl(t\cdot(g_{21},g_{22})\bigr)\,(\mu\nu^{-1})(t)\,\|t\|^{2s+1}\,d\nu_0(t)$$ is the Godement section attached to $\Phi$, $\mu$, $\nu$ and to the positive module character $\alpha$ of $\mathbb{A}_F^\times$ coming from the Haar distribution character of $\mathbb{A}_F$, with $\|\cdot\|$ the idele norm.
--
--   This is Godement's absolute convergence lemma for the Godement–Eisenstein family attached to a Schwartz–Bruhat function in two adelic variables: the Bruhat decomposition $B(F)\backslash\mathrm{GL}_2(F)=\{1\}\sqcup\{w\,n(\xi):\xi\in F\}$ reduces convergence of the Eisenstein series to the series summed here, and the bound holds at every point of $\mathrm{GL}_2(\mathbb{A}_F)$, not merely almost everywhere. It supplies the everywhere-summability input for the unfolding of the Rankin–Selberg integral against the Godement–Eisenstein series used in the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_summable_norm_godementSection_adelicWeyl_unipotentGL2_mul_of_mem_schwartzBruhat2_of_half_lt_re.lean

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_AutomorphicForm_InducedSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel LanglandsTunnell.RankinSelberg

theorem AutomorphicForm.summable_norm_godementSection_adelicWeyl_unipotentGL2_mul_of_mem_schwartzBruhat2_of_half_lt_re
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsIdeleClassChar (𝓞 F) F μ) (hν : IsIdeleClassChar (𝓞 F) F ν)
    (hμu : IsUnitaryChar (𝓞 F) F μ) (hνu : IsUnitaryChar (𝓞 F) F ν)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ schwartzBruhat2 F)
    (s : ℂ) (hs : 1 / 2 < s.re) :
    ∀ g : AdelicGL2 (𝓞 F) F, Summable fun ξ : F =>
      ‖godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s
        (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖ := by sorry
