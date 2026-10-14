-- Prove2me | Theorems.Thm_FirstPriceLearning_ContextLowerBound_property_5
-- name    : FirstPriceLearning.ContextLowerBound.property_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:08.866977+00:00
-- url     : https://prove2.me/theorems/3747921f-2ef8-468f-b4f5-ef5969c6e769
-- title:
--   Property 5: KL divergence of the observed rewards when one coordinate of $u$ is reset
-- statement:
--   Let $K=(\alpha+1)M\le T$, $\Delta=\sqrt{K/(16T)}$, $u\in\{0,1,\dots,\alpha\}^M$ and a context $c$ with $u_c\ne0$, and let $u'=(u_1,\dots,u_{c-1},0,u_{c+1},\dots,u_M)$. For an action $(i,j)$ write $P^u(i,j)$ for the law of the rewards revealed when $(i,j)$ is chosen (the rewards of $(i,j)$ and its out-neighbours in $G$, under every context). Then
--   $$D_{\mathrm{KL}}\big(P^{u'}(i,j)\,\|\,P^u(i,j)\big)=\begin{cases}0 & \text{if } i>c \text{ or } (i=c,\ j\neq u_c),\\ D_{\mathrm{KL}}\big(\mathrm{Bern}(1/4)\,\|\,\mathrm{Bern}(1/4+2\Delta)\big) & \text{if } i<c \text{ or } (i,j)=(c,u_c),\end{cases}$$
--   and in both cases
--   $$D_{\mathrm{KL}}\big(P^{u'}(i,j)\,\|\,P^u(i,j)\big)\le\frac{64}{3}\Delta^2\cdot\mathbb 1\big(i<c\ \text{or}\ (i,j)=(c,u_c)\big).$$
--
--   This quantifies how much information each action carries about the $c$-th coordinate of $u$; it feeds the chain rule of KL divergence in the proof of Theorem 6.
--
--   **Formalization Note.** The paper states the property for every $u$; for $u_c=0$ we have $u'=u$ and the divergence is $0$, so the printed case split concerns $u_c\ne0$, which is assumed here. KL divergence is Mathlib's $[0,\infty]$-valued `klDiv`. The observed law is the image of $P^u$ under masking of the unrevealed coordinates.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 22, proof of Theorem 6, property 5

import Mathlib
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Model
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Construction

open MeasureTheory InformationTheory

namespace FirstPriceLearning.ContextLowerBound

theorem property_5 (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (hu : u c ≠ 0) (a : Act M α) :
    klDiv (observedLaw M α T (Function.update u c 0) a) (observedLaw M α T u a) =
        (if a.1 < c ∨ a = (c, u c) then
          klDiv (bernoulliReal (1 / 4)) (bernoulliReal (1 / 4 + 2 * gap M α T))
        else 0) ∧
      klDiv (observedLaw M α T (Function.update u c 0) a) (observedLaw M α T u a) ≤
        ENNReal.ofReal
          (64 / 3 * gap M α T ^ 2 * (if a.1 < c ∨ a = (c, u c) then 1 else 0)) := by sorry

end FirstPriceLearning.ContextLowerBound
