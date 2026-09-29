-- Prove2me | Theorems.Thm_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_restrict_eq
-- name    : AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family_of_restrict_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/c3e5c186-8604-5ff4-a719-bf3529da179b
-- title:
--   Uniform pure-tensor big-cell expansion of flat induced families
-- statement:
--   Let $F$ be a number field and let $\alpha\colon \mathbb{A}_F^\times \to \mathbb{R}^\times$ be the unit-group homomorphism obtained from the distributive Haar character of the adele ring $\mathbb{A}_F$ composed with $\mathbb{R}_{\ge 0}\to\mathbb{R}$, assumed pointwise positive ($h\alpha$). For every function $\varphi_0$ on $\mathrm{GL}_2(\mathbb{A}_F)$ there exist a finite set $S$ of finite places of $F$, an $n$, constants $c_j\in\mathbb{C}$, integers $k_{j,i}$ indexed by the real places, triples $(a_{j,w},b_{j,w},m_{j,w})$ of naturals indexed by the complex places with $a_{j,w}+b_{j,w}\le m_{j,w}$, a depth $m\ge 1$, and functions $A_{j,v},B_{j,v}\colon F_v\to\mathbb{C}$ such that $A_{j,v}$ is constant on congruence classes modulo $\mathfrak{p}_v^m$ inside the valuation ring and $B_{j,v}$ is constant on all congruence classes modulo $\mathfrak{p}_v^m$ in $F_v$, for $v\in S$, with the following property, holding for all data chosen afterwards. Let $\mu,\nu\colon\mathbb{A}_F^\times\to\mathbb{C}^\times$ be homomorphisms and let $\varphi\colon\mathbb{C}\times \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family such that each $\varphi_s$ satisfies $\varphi_s(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi_s(g)$ for $b$ in the adelic Borel subgroup (lower-left entry zero), where $\eta_1=\mu\cdot\alpha^{s+1/2}$ and $\eta_2=\nu\cdot\alpha^{-(s+1/2)}$; each $\varphi_s$ is archimedean $K$-finite, in the sense that at every infinite place the right translates by the row-isometry subgroup span a finite-dimensional space; each $\varphi_s$ is $K_f$-smooth, i.e. its stabiliser in the kernel of the archimedean projection is open; each $\varphi_s$ is continuous; $\varphi_s(k)=\varphi_0(k)$ whenever the finite part of $k$ lies in $\mathrm{GL}_2$ of the finite integral adeles and all archimedean components of $k$ are row isometries (determinant of norm one, preserving the sum of squared norms of the two row-combinations); and $\varphi_s(g)\ne 0$ for some $s,g$. Then, writing $\chi=\mu\nu^{-1}$, there exist functions $R_i,R_w$ of a real variable indexed by the real and the complex places such that: the local component of $\chi$ at $v\notin S$ is trivial on units of valuation one; at each $v\in S$ it is trivial on some group of higher units; $R_i$ and $R_w$ compute $\chi(\iota_i(u))$, respectively $\chi(\iota_w(u))$, on positive elements of the real completions and on positive reals hit by the complex embedding; $(-1)^{k_{j,i}}=\chi(\iota_i(-1))$ at each real place; at a complex place $w$ at which $\chi$ is non-trivial on some unit of absolute value one, no $j$ has $a_{j,w}=b_{j,w}$ together with $m_{j,w}=2a_{j,w}$; and for every $s\in\mathbb{C}$ and every adele $x$, the value $\varphi_s(w_0^{-1}n(x))$ at the big-cell point, $w_0$ the image of the antidiagonal Weyl element and $n(x)$ the upper unipotent matrix, equals $\sum_j c_j$ times the product over the real places of $R_i((1+x_i^2)^{-1/2})\,((x_i-\sqrt{-1})/\sqrt{1+x_i^2})^{k_{j,i}}(1+x_i^2)^{-(s+1/2)}$, times the product over the complex places of $R_w((1+\|x_w\|^2)^{-1/2})\,x_w^{a_{j,w}}\bar{x}_w^{\,b_{j,w}}(1+\|x_w\|^2)^{-(2s+1)-m_{j,w}/2}$, times the product over $v\in S$ of $A_{j,v}(x_v)$ on the valuation ring and $\chi_v^{-1}(x_v)\,|x_v|_v^{-(2s+1)}B_{j,v}(x_v^{-1})$ off it, times the finitely-supported product over $v\notin S$ of $1$ on the valuation ring and $\chi_v^{-1}(x_v)\,|x_v|_v^{-(2s+1)}$ off it, the local absolute value being the Haar modulus.
--
--   This is the expansion of a flat family of $K$-finite induced sections along the big cell of $\mathrm{GL}_2$ over a number field as a finite sum of pure tensors, with the quantifiers arranged so that the tensor data — the ramification set $S$, the number of terms, the coefficients, the archimedean types and the level-$m$ locally constant finite-place factors — depend only on the common restriction $\varphi_0$ to the maximal compact subgroup, while the characters $\mu,\nu$ enter only through the explicit character factors $R$ and $\chi_v^{-1}|\cdot|_v^{-(2s+1)}$. It underlies the uniform estimates for Weyl intertwining integrals and the uniform factorisation data used in the construction of Eisenstein pieces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_restrict_eq.lean

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
open AutomorphicForm
open AutomorphicForm.WindowedSiegel
open scoped NNReal

open scoped Classical in

theorem AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family_of_restrict_eq
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (φ₀ : AdelicGL2 (𝓞 F) F → ℂ),
      ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) (c : Fin n → ℂ)
        (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
        (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
        (m : ℕ) (A B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ),
        (∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}),
          (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2) ∧
        1 ≤ m ∧
        (∀ (j : Fin n), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F,
          ∀ y ∈ v.adicCompletionIntegers F,
            Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A j v y = A j v x) ∧
        (∀ (j : Fin n), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
          Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B j v y = B j v x) ∧
        ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
          (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
          (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
          (_hφK : ∀ s, IsArchKFinite F (φ s))
          (_hφf : ∀ s, IsKfSmooth F (φ s))
          (_hφc : ∀ s, Continuous (φ s))
          (_hφ₀ : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 F) F),
              glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
              (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
              φ s k = φ₀ k)
          (_hφne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g ≠ 0),
        ∃ (Rr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
          (Rc : {w : InfinitePlace F // w.IsComplex} → ℝ → ℂ),
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
        (∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}),
          (-1 : ℂ) ^ (kdat j i)
            = (((μ * ν⁻¹)
                  (NumberField.TateGlobal.archUnitHom i.1 (-1 : (i.1.Completion)ˣ)) : ℂˣ) : ℂ)) ∧
        (∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}) (u : (w.1.Completion)ˣ),
          ‖Completion.extensionEmbedding w.1 (u : w.1.Completion)‖ = 1 →
          (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom w.1 u) : ℂˣ) : ℂ) ≠ 1 →
          ¬ ((abm j w).1 = (abm j w).2.1 ∧ (abm j w).2.2 = 2 * (abm j w).1)) ∧
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
