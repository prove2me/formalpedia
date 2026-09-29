-- Prove2me | Theorems.Thm_AutomorphicForm_exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_ball
-- name    : AutomorphicForm.exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_ball
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/efbd5eb0-1526-57d5-b8ec-8f95411f0298
-- title:
--   Unipotent surgery concentrating a Whittaker coefficient on a small ball
-- statement:
--   Let $K$ be a number field, let $D$ be a subset of $\mathrm{GL}_2(\mathbb{A}_K)$ and let $G:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ satisfy $G(n(\iota(\beta)+u)h)=G(n(u)h)$ for all $\beta\in K$, all adeles $u$ and all $h$, where $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\iota:K\to\mathbb{A}_K$ is the structure map, and suppose that for every $\alpha\in K$ and every $g$ the function $x\mapsto G(n(x)g)\,\psi(-\iota(\alpha)x)$ is integrable for the additive Haar measure of $\mathbb{A}_K$ conditioned on the adelic box (archimedean box times the integral finite adeles), $\psi$ being the standard additive character of $\mathbb{A}_K$; the remaining data of the pins are the window $D$, central subgroup $\top$, the levels $N\mapsto \mathtt{levelOne}\sqcap\mathtt{finiteAdelicGL2Subgroup}$ and the Hecke generators $\mathtt{heckeGen}$. Let $S$ be a finite set of finite places of $K$, $m,n\in\mathbb{N}$ with $n>0$, and $t_0$ an idele unit. Then there exist $r\in\mathbb{N}$, adeles $y_1,\dots,y_r$ and scalars $c_1,\dots,c_r\in\mathbb{C}$ such that: each $y_i$ has zero archimedean component and finite component vanishing outside $S$; each $n(y_i)$ commutes with the image of every $x_v\in\mathrm{GL}_2(K_v)$ under the place embedding, for every $v\notin S$; for every idele unit $t$ and every $g'$ commuting with all $n(y_i)$, the Whittaker coefficient at $\alpha=1$ of $g\mapsto\sum_i c_i\,G(g\,n(y_i))$ at $\mathrm{diag}(t,1)g'$ equals $\bigl(\sum_i c_i\,\psi(t\,y_i)\bigr)$ times the Whittaker coefficient of $G$ at $\alpha=1$ and $\mathrm{diag}(t,1)g'$; and for every idele unit $t$ with $|t_v|\le q_v^{\,m}$ in the sense $\mathrm{v}(t_v)\le \mathrm{ofAdd}(m)$ for all $v\in S$, the multiplier $\sum_i c_i\,\psi(t\,y_i)$ equals $1$ if $\mathrm{v}(t_v-t_{0,v})\le \mathrm{v}(t_{0,v})\cdot\mathrm{ofAdd}(-n)$ for all $v\in S$, and $0$ otherwise.
--
--   This is the Kirillov-model surgery at a finite set of places: right translation by unipotents $n(y)$ multiplies the Whittaker coefficient along the torus by the character $t\mapsto\psi(ty)$, and a finite combination of such characters reproduces, on a prescribed box, the indicator of the ball $t_v\in t_{0,v}(1+\mathfrak{p}_v^{\,n})$ at every $v\in S$. It is used in the construction of Rankin–Selberg test data, namely by [`AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero`](thm.html#AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_ball.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm IsDedekindDomain
open scoped Classical

theorem AutomorphicForm.exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_ball
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (G : AdelicGL2 (𝓞 K) K → ℂ)
    (hper : ∀ (β : K) (u : AdeleRing (𝓞 K) K) (h : AdelicGL2 (𝓞 K) K),
      G (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * h) = G (unipotentGL2 u * h))
    (hint : ∀ (α : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
      (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) G α g)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) (t₀ : (AdeleRing (𝓞 K) K)ˣ) (n : ℕ) (hn : 0 < n) :
    ∃ (r : ℕ) (y : Fin r → AdeleRing (𝓞 K) K) (cs : Fin r → ℂ),
      (∀ i, (y i).1 = 0 ∧ ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → (y i).2 w = 0) ∧
      (∀ i, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
        unipotentGL2 (y i) * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * unipotentGL2 (y i)) ∧
      (∀ (t : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
        (∀ i, g' * unipotentGL2 (y i) = unipotentGL2 (y i) * g') →
        whittakerCoefficient K
            (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
              (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
            (fun g => ∑ i, cs i * G (g * unipotentGL2 (y i))) 1 (diagOne t * g') =
          (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) *
            whittakerCoefficient K
              (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) G 1 (diagOne t * g')) ∧
      (∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) ≤
            ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) =
          if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) *
                ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0) := by sorry
