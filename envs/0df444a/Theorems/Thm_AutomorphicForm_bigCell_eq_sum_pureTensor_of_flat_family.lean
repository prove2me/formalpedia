-- Prove2me | Theorems.Thm_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family
-- name    : AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/0be9b9f4-2333-5f0b-b706-8e359c035683
-- title:
--   Big-cell values of a flat K-finite family as pure tensors
-- statement:
--   Let $F$ be a number field and let $\alpha\colon\mathbb{A}_F^\times\to\mathbb{R}^\times$ be the homomorphism to units obtained from the distributive Haar character of the adele ring $\mathbb{A}_F$ by pushing its $\mathbb{R}_{\ge0}$-values into $\mathbb{R}$; assume all its values are positive ($h\alpha$). Let $\mu,\nu\colon\mathbb{A}_F^\times\to\mathbb{C}^\times$ be monoid homomorphisms (no continuity assumed), put $\chi=\mu\nu^{-1}$, and let $\varphi\colon\mathbb{C}\to(\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C})$ be a family such that for every $s$: (i) $\varphi_s$ is an induced section for the pair $(\mu\cdot\alpha^{s+1/2},\,\nu\cdot\alpha^{-(s+1/2)})$, i.e. $\varphi_s(bg)=\mu\alpha^{s+1/2}(b_{00})\,\nu\alpha^{-(s+1/2)}(b_{11})\,\varphi_s(g)$ for all $g$ and all $b$ in the adelic Borel subgroup (lower-left entry zero); (ii) at each infinite place $w$ the right translates of $\varphi_s$ along `archRowIsometrySubgroup F w` satisfy `RightTranslatesSpanFinite`; (iii) the stabiliser of $\varphi_s$ for right translation by the kernel of `glArch` (matrices with trivial archimedean part) is open; (iv) $\varphi_s$ is continuous. Assume the family is flat: $\varphi_s(k)=\varphi_{s'}(k)$ whenever the finite part of $k$ lies in `finiteIntegralGL2` and each archimedean component of $k$ is a row isometry (unit determinant norm, and the row action preserves $\|x\|^2+\|y\|^2$); and assume $\varphi_s(g)\ne0$ for some $s,g$. Then there are a finite set $S$ of finite places, $n\in\mathbb{N}$, coefficients $c_j\in\mathbb{C}$, integers $k_{j,i}$ at real places $i$, triples $(a_{j,w},b_{j,w},m_{j,w})$ at complex places $w$ with $a_{j,w}+b_{j,w}\le m_{j,w}$, an integer $m\ge1$, functions $A_{j,v},B_{j,v}$ on the completions at finite places, and $R_{r,i},R_{c,w}\colon\mathbb{R}\to\mathbb{C}$, such that: $A_{j,v}$ is constant on balls $v(y-x)\le q_v^{-m}$ inside the local integers and $B_{j,v}$ is constant on such balls in all of $F_v$, for $v\in S$; the local character $\chi_v$ (obtained from $\chi$ by the idele with component $u$ at $v$ and $1$ elsewhere) is trivial on units of valuation $1$ for $v\notin S$, and trivial on `higherUnitsAt F v cN` for some $cN$ when $v\in S$; $R_{r,i}$ and $R_{c,w}$ compute $\chi$ on archimedean central units mapping to positive reals; and for all $s\in\mathbb{C}$ and all adeles $x$, $\varphi_s(w^{-1}\,n(x))$, with $w$ the adelic Weyl element and $n(x)$ the upper unipotent with entry $x$, equals $\sum_{j<n}c_j$ times the product of: over real places $i$, $R_{r,i}\big((1+x_i^2)^{-1/2}\big)\big((x_i-\mathrm{i})/\sqrt{1+x_i^2}\big)^{k_{j,i}}(1+x_i^2)^{-(s+1/2)}$; over complex places $w$, $R_{c,w}\big((1+\|x_w\|^2)^{-1/2}\big)\,x_w^{a_{j,w}}\bar{x}_w^{b_{j,w}}(1+\|x_w\|^2)^{-(2s+1)-m_{j,w}/2}$; over $v\in S$, the value at $x_v$ of $A_{j,v}$ on the local integers plus, off them, $\chi_v^{-1}(y)\,|y|^{-(2s+1)}B_{j,v}(y^{-1})$ (with $\chi_v^{-1}$ extended by $0$ and $|\cdot|$ the local modulus); and the multipliable product over $v\notin S$ of the same expression with $A_{j,v}$ and $B_{j,v}$ replaced by $1$.
--
--   This is the Bruhat big-cell factorisation of a flat, $K$-finite, $K_f$-smooth family of induced sections on $\mathrm{GL}_2$ over the adeles: on the big cell $w^{-1}N(\mathbb{A}_F)$ the family is a finite sum of pure tensors, with explicit archimedean factors of weight type and, at finite places, locally constant data together with the unramified Tate factors outside a finite set $S$. It is the input to the place-by-place evaluation of the Weyl intertwining integral, and is used for the Euler-product bound and the limit statements for the intertwining integral near $s=1/2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family.lean

import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal
open scoped Classical in

theorem AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφc : ∀ s, Continuous (φ s))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k)
      (_hφne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g ≠ 0),
      ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) (c : Fin n → ℂ)
        (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
        (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
        (m : ℕ) (A B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
        (Rr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
        (Rc : {w : InfinitePlace F // w.IsComplex} → ℝ → ℂ),
        (∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}),
          (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2) ∧
        1 ≤ m ∧
        (∀ (j : Fin n), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F,
          ∀ y ∈ v.adicCompletionIntegers F,
            Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A j v y = A j v x) ∧
        (∀ (j : Fin n), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
          Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B j v y = B j v x) ∧
        (∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
          NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1) ∧
        (∀ v ∈ S, ∃ cN : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v cN,
          NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1) ∧
        (∀ (i : {w : InfinitePlace F // w.IsReal}) (u : (i.1.Completion)ˣ),
          0 < Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion) →
          Rr i (Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion))
            = (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom i.1 u) : ℂˣ) : ℂ)) ∧
        (∀ (w : {w : InfinitePlace F // w.IsComplex}) (u : (w.1.Completion)ˣ) (r : ℝ), 0 < r →
          Completion.extensionEmbedding w.1 (u : w.1.Completion) = (r : ℂ) →
          Rc w r = (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom w.1 u) : ℂˣ) : ℂ)) ∧
        ∀ (s : ℂ) (x : AdeleRing (𝓞 F) F),
          φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)
            = ∑ j : Fin n, c j
                * (∏ i : {w : InfinitePlace F // w.IsReal},
                    Rr i ((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2)
                            ^ (-(1 / 2 : ℝ)))
                      * ((((Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) : ℝ) : ℂ)
                            - Complex.I)
                          / ((Real.sqrt (1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2)
                              : ℝ) : ℂ)) ^ (kdat j i)
                      * (((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2 : ℝ) : ℂ))
                          ^ (-(s + 1 / 2)))
                * (∏ w : {w : InfinitePlace F // w.IsComplex},
                    Rc w ((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2)
                            ^ (-(1 / 2 : ℝ)))
                      * Completion.extensionEmbedding w.1 (x.1 w.1) ^ (abm j w).1
                      * (starRingEnd ℂ) (Completion.extensionEmbedding w.1 (x.1 w.1))
                          ^ (abm j w).2.1
                      * (((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2 : ℝ) : ℂ))
                          ^ (-(2 * s + 1) - ((abm j w).2.2 : ℂ) / 2))
                * (∏ v ∈ S,
                    ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) (x.2 v)
                      + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                          (fun y => LanglandsTunnell.TateLocal.charExt
                              (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
                            * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))
                            * B j v y⁻¹) (x.2 v)))
                * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                    ((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
                        (fun _ => (1 : ℂ)) (x.2 v.1)
                      + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
                          (fun y => LanglandsTunnell.TateLocal.charExt
                              (NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1)⁻¹ y
                            * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)))
                          (x.2 v.1)) := by sorry
