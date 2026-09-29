-- Prove2me | Theorems.Thm_AutomorphicForm_exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_shell
-- name    : AutomorphicForm.exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_shell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/f3bf57a0-7f0a-5599-990a-51c4b0208450
-- title:
--   Unipotent surgery cutting a Whittaker function to a valuation shell
-- statement:
--   Let $K$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_K)$ and $G:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ a function which is invariant under left translation by rational upper unipotents, in the sense that $G(n(\iota(\beta)+u)h)=G(n(u)h)$ for all $\beta\in K$, all adeles $u$ and all $h$, where $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; assume further that for every $\alpha\in K$ and every $g$ the integrand $x\mapsto G(n(x)g)\,\psi(-\alpha x)$ is integrable for the measure of the production pins attached to $D$, the levels $N\mapsto \mathtt{levelOne}\sqcap\mathtt{finiteAdelicGL2Subgroup}$, the Hecke generators $\mathtt{heckeGen}$ and the adelic box (adelic additive Haar measure conditioned on the box), $\psi$ being the standard additive character of $\mathbb{A}_K$. Let $S$ be a finite set of finite places of $K$, let $m\in\mathbb{N}$ and let $a$ assign an integer to each finite place. Then there are $r\in\mathbb{N}$, adeles $y_1,\dots,y_r$ and scalars $c_1,\dots,c_r\in\mathbb{C}$ such that: each $y_i$ has zero archimedean component and finite component vanishing outside $S$; each $n(y_i)$ commutes with the image in $\mathrm{GL}_2(\mathbb{A}_K)$ of every element of $\mathrm{GL}_2(K_v)$ for $v\notin S$; for every idele $t$ and every $g'$ commuting with all $n(y_i)$, the Whittaker coefficient at $\alpha=1$ of $g\mapsto\sum_i c_i G(g\,n(y_i))$ at $\mathrm{diag}(t,1)g'$ equals $\bigl(\sum_i c_i\psi(t y_i)\bigr)$ times the Whittaker coefficient at $\alpha=1$ of $G$ at $\mathrm{diag}(t,1)g'$; and for every idele $t$ whose components satisfy $\mathrm{v}(t_v)\le\mathrm{ofAdd}(m)$ for all $v\in S$, the multiplier $\sum_i c_i\psi(t y_i)$ equals $1$ if $\mathrm{v}(t_v)=\mathrm{ofAdd}(a_v)$ for every $v\in S$, and $0$ otherwise.
--
--   This is surgery in the Kirillov model at a finite set of bad places: right translation by unipotents $n(y)$ multiplies the $\psi$-Whittaker coefficient along the diagonal torus by $\psi(ty)$, so a finite linear combination of such translates can be arranged to cut the torus variable down to a prescribed valuation shell at the places of $S$ while leaving the behaviour outside $S$ untouched. It is used in the construction of test data for the Rankin–Selberg integral, in [`AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_self_analyticOnNhd_re_pos`](thm.html#AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_self_analyticOnNhd_re_pos).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_shell.lean

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

theorem AutomorphicForm.exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_shell
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (G : AdelicGL2 (𝓞 K) K → ℂ)
    (hper : ∀ (β : K) (u : AdeleRing (𝓞 K) K) (h : AdelicGL2 (𝓞 K) K),
      G (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * h) = G (unipotentGL2 u * h))
    (hint : ∀ (α : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
      (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) G α g)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) (a : HeightOneSpectrum (𝓞 K) → ℤ) :
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
          if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) =
              ((Multiplicative.ofAdd (a v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0) := by sorry
