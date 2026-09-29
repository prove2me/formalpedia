-- Prove2me | Theorems.Thm_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity
-- name    : AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/d1772937-8145-5a7c-8713-c96ebe9d4709
-- title:
--   Big-cell pure-tensor decomposition with archimedean type parity
-- statement:
--   Let $F$ be a number field and let $\alpha\colon \mathbb{A}_F^\times \to \mathbb{R}^\times$ be the unit-group homomorphism obtained from the Haar-scaling character `distribHaarChar` of $\mathbb{A}_F$ pushed along $\mathbb{R}_{\ge 0}\to\mathbb{R}$, and assume $\alpha(x)>0$ for all $x$. Let $\mu,\nu\colon \mathbb{A}_F^\times\to\mathbb{C}^\times$ be quasi-characters and let $\varphi\colon\mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family such that, for each $s$: $\varphi_s(bg)=\mu\alpha^{s+1/2}(b_{11})\,\nu\alpha^{-(s+1/2)}(b_{22})\,\varphi_s(g)$ for all $b$ in the adelic Borel subgroup (lower-left entry zero) and all $g$; the right translates of $\varphi_s$ under the row-isometry subgroup at each infinite place span a finite-dimensional space; the stabiliser of $\varphi_s$ for right translation inside the kernel of the archimedean projection is open; and $\varphi_s$ is continuous. Assume further flatness, namely $\varphi_s(k)=\varphi_{s'}(k)$ whenever the finite part of $k$ is integral at all places and every archimedean component of $k$ satisfies `IsRowIsometry`, and that $\varphi_s(g)\neq 0$ for some $s,g$. Then there are: a finite set $S$ of finite places; $n\in\mathbb{N}$ and coefficients $c_j\in\mathbb{C}$; integers $k_{j,i}$ at the real places and triples $(a_{j,w},b_{j,w},m_{j,w})\in\mathbb{N}^3$ with $a_{j,w}+b_{j,w}\le m_{j,w}$ at the complex places; an integer $m\ge 1$; functions $A_{j,v},B_{j,v}\colon F_v\to\mathbb{C}$; and functions $R_i,R_w$ of a real variable at the real and complex places, subject to: $A_{j,v}$ is constant on classes modulo $\mathfrak{p}_v^m$ inside $\mathcal{O}_v$ and $B_{j,v}$ is constant on classes modulo $\mathfrak{p}_v^m$ in all of $F_v$, for $v\in S$; the local component of $\chi=\mu\nu^{-1}$ at $v$ is trivial on the norm-one units for $v\notin S$ and trivial on some group of higher units at each $v\in S$; $R_i$ evaluated at the image of a unit with positive real embedding equals $\chi$ of the corresponding idele supported at $i$, and likewise $R_w(r)=\chi(\cdot)$ whenever a unit at the complex place $w$ has embedding equal to $r>0$; the parity condition $(-1)^{k_{j,i}}=\chi$ of the idele with $-1$ at the real place $i$; and, at a complex place $w$, if some unit of absolute value one has $\chi$-value $\neq 1$ then it is not the case that $a_{j,w}=b_{j,w}$ and $m_{j,w}=2a_{j,w}$. Finally, for every $s\in\mathbb{C}$ and every adele $x$, the value $\varphi_s\bigl(w_0^{-1}\,n(x)\bigr)$, where $w_0$ is the adelic image of $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, equals $\sum_{j<n} c_j$ times a pure tensor: at each real place $i$ the factor $R_i\bigl((1+x_i^2)^{-1/2}\bigr)\bigl((x_i-\sqrt{-1})/\sqrt{1+x_i^2}\bigr)^{k_{j,i}}(1+x_i^2)^{-(s+1/2)}$; at each complex place $w$ the factor $R_w\bigl((1+\|z_w\|^2)^{-1/2}\bigr)z_w^{a_{j,w}}\overline{z_w}^{\,b_{j,w}}(1+\|z_w\|^2)^{-(2s+1)-m_{j,w}/2}$; at each $v\in S$ the sum of $A_{j,v}(x_v)$ on $\mathcal{O}_v$ and, off $\mathcal{O}_v$, of $\chi_v^{-1}(x_v)\,|x_v|^{-(2s+1)}B_{j,v}(x_v^{-1})$, where the absolute value is the local Haar modulus; and a multipliable product over $v\notin S$ of the same expression with $A$ and $B$ replaced by $1$.
--
--   This is the big-cell decomposition of a flat, $K$-finite family of principal-series sections on $\mathrm{GL}_2$ over a number field: restricted to the big Bruhat cell $w_0^{-1}N(\mathbb{A}_F)$, such a family is a finite sum of pure tensors of archimedean Whittaker-type factors and local Tate integrands, with the archimedean weights $k_{j,i}$ and $(a_{j,w},b_{j,w},m_{j,w})$ constrained by the central character $\mu\nu^{-1}$ at $-1$ and on the unit circle. It is the input to the meromorphic continuation of the Weyl-element intertwining integral and of its normalisation by completed $L$-factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.lean

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

theorem AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity
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
