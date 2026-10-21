-- Prove2me | Theorems.Thm_EpiControl_SinglePeak_lemma_9_multipliers
-- name    : EpiControl.SinglePeak.lemma_9_multipliers
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:26.697649+00:00
-- url     : https://prove2.me/theorems/66ffc826-7353-4306-a440-0b5330711818
-- title:
--   Lemma 9 (second part), p. 15 (PDF 16) — Lagrange multipliers λ∗₁, λ∗₂ satisfying (11)–(13)
-- statement:
--   Let $\beta^*$ be an optimal control with SIR path $(s^*,i^*)$. Then there are absolutely continuous $\lambda_1^*,\lambda_2^*:[0,T]\to\mathbb R$ such that, for almost every $t\in[0,T]$,
--   $$(\lambda_1^*)'(t)=(\lambda_1^*(t)-\lambda_2^*(t))\beta^*(t)i^*(t),\qquad \lambda_1^*(T)=0,$$
--   $$(\lambda_2^*)'(t)=(\lambda_1^*(t)-\lambda_2^*(t))\beta^*(t)s^*(t)+\gamma\lambda_2^*(t)-v'(i^*(t)),\qquad \lambda_2^*(T)=\frac{v(i^*(T))}{\gamma i^*(T)}, \tag{11}$$
--   and
--   $$\beta^*(t)\in\arg\min_{b\in B}\big[(\lambda_2^*(t)-\lambda_1^*(t))i^*(t)s^*(t)b+c(b)\big], \tag{12}$$
--   and moreover, for every $t\in[0,T]$,
--   $$M\big((\lambda_2^*(t)-\lambda_1^*(t))i^*(t)s^*(t)\big)-\gamma\lambda_2^*(t)i^*(t)+v(i^*(t))=M\Big(\frac{v(i^*(T))s^*(T)}{\gamma}\Big). \tag{13}$$
--
--   This is the Pontryagin principle for the problem; (13) is the constancy of the maximized Hamiltonian.
--
--   **Formalization Note** Absolute continuity and (11) are expressed by continuity of $\lambda_1,\lambda_2$ on $[0,T]$ together with the integral form $\lambda_k(t)=\lambda_k(T)-\int_t^T\lambda_k'(r)\,dr$; (12) holds almost everywhere on $[0,T]$. The platform's general Pontryagin principles do not apply (their Lipschitz or smoothness hypotheses fail here), so the statement is posed directly.
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), p. 15 (PDF 16), Lemma 9, (11)–(13)

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiControl.SinglePeak

theorem lemma_9_multipliers (P : Params) (hP : P.Standing) (β s i : ℝ → ℝ)
    (hopt : P.IsOptimal β s i) :
    ∃ lam1 lam2 : ℝ → ℝ, P.IsMultiplier β s i lam1 lam2 := by sorry
end EpiControl.SinglePeak
