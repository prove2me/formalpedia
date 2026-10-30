-- Prove2me | Theorems.Thm_EPRPharma_lemma_1_doctor_prescription
-- name    : EPRPharma.lemma_1_doctor_prescription
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:21:55.651972+00:00
-- url     : https://prove2.me/theorems/48827a11-124b-449d-897e-08c9afe33b03
-- title:
--   Lemma 1: the doctor prescribes the need or the whole unit
-- statement:
--   Let $(p,\eta_d,\eta_p)$ be any decision of the producer and $\theta_n\in[0,1]$ the patient's need. Then the doctor's prescription is
--
--   $$q_p^*(\theta_n)=\begin{cases}\theta_n, & \eta_d<p+o_d(1-\eta_p),\\ 1, & \eta_d\ge p+o_d(1-\eta_p).\end{cases}$$
--
--   The doctor over-prescribes exactly when the marginal promotional benefit $\eta_d$ is at least the marginal cost $p+o_d(1-\eta_p)$ of a further unit. This splits the producer's decisions into the two regions used throughout the paper.
--
--   Differences from the source:
--
--   - reading: the doctor's prescription q*_p = argmax U_d(q_p) over θ_n ≤ q_p ≤ 1 (p. 10) → the largest maximizer of U_d on [θ_n, 1] (doctorQ); reason: U_d is affine in q_p, so the maximizer is unique except at η_d = p + o_d(1 − η_p), where every q_p ties and Lemma 1 and its proof (App. p. 1) say the doctor over-prescribes (q*_p = 1)
--   - generalization: 'equal to the patient's need if p − u_p ≤ η_d < p + o_d(1 − η_p)' → doctorQ = θ_n whenever η_d < p + o_d(1 − η_p); reason: p − u_p ≤ η_d is the doctor's participation and plays no role in her choice; the statement specializes to the printed one
--   - reading: 'beyond the patient's need if η_d ≥ p + o_d(1 − η_p)' → doctorQ = 1 for every θ_n ∈ [0, 1]; reason: the proof (App. p. 1) states q*_p = 1 ≥ θ_n; at θ_n = 1 no quantity exceeds the need, and 1 > θ_n for θ_n < 1
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), Lemma 1, p. 15, and its proof, Online Appendix p. 1

import Mathlib
import Definitions.Def_EPRPharma_doctorQ

namespace EPRPharma

/-- **Lemma 1: the doctor prescribes the need if η_d < p + o_d(1 − η_p) and the whole unit
otherwise.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), Lemma 1, p. 15:
"The doctor provides a prescription that is equal to the patient's need if p − u_p ≤ η_d <
p + o_d (1 − η_p) and beyond the patient's need if η_d ≥ p + o_d (1 − η_p)." Its proof (Online
Appendix p. 1) gives q*_p = θ_n in the first case and q*_p = 1 in the second.

For every parameter vector, every decision (p, η_d, η_p) and every need θ_n ∈ [0, 1]: if
η_d < p + o_d(1 − η_p) then q*_p(θ_n) = θ_n, and if η_d ≥ p + o_d(1 − η_p) then q*_p(θ_n) = 1.

**Formalization Note.** The first clause drops the printed condition p − u_p ≤ η_d, which is the
doctor's participation and plays no role in her choice (generalization). At the tie
η_d = p + o_d(1 − η_p) the doctor prescribes the largest maximizer (`doctorQ`). -/
theorem lemma_1_doctor_prescription (P : Params) (d : Decision) (θn : ℝ)
    (hθ : θn ∈ Set.Icc (0:ℝ) 1) :
    (d.etaD < d.p + P.od * (1 - d.etaP) → doctorQ P d θn = θn) ∧
      (d.p + P.od * (1 - d.etaP) ≤ d.etaD → doctorQ P d θn = 1) := by sorry

end EPRPharma
