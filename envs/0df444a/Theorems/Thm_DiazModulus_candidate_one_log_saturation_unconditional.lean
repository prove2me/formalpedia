-- Prove2me | Theorems.Thm_DiazModulus_candidate_one_log_saturation_unconditional
-- name    : DiazModulus.candidate_one_log_saturation_unconditional
-- status  : Open
-- author  : @carlok
-- created : 2026-10-02T11:28:44.59998+00:00
-- url     : https://prove2.me/theorems/b6fa5e39-dced-4c6f-94af-c88e74976fe1
-- title:
--   A candidate in $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}\ell$ is a rational multiple of $\ell$; no candidate is $a + b\pi$; unconditionally
-- statement:
--   Let $u$ be a candidate: $u \neq 0$ with $|u|$ and $e^{u}$ algebraic. If $u = a + b\ell$ with $a, b$ algebraic and $\ell$ a logarithm of an algebraic number, then $u = r\ell$ for some $r \in \mathbb{Q}$; and $u \neq a + b\pi$ for all algebraic $a, b$.
--
--   This is `DiazModulus.candidate_one_log_saturation` with both of its hypotheses discharged: Baker's theorem for two logarithms by `DiazModulus.baker_two_logs`, proved in this mission following Chapter 4 of Waldschmidt's book, and Hermite–Lindemann by `DiazModulus.hermite_lindemann_holds`.
--
--   **Proof.** `DiazModulus.candidate_one_log_saturation DiazModulus.baker_two_logs DiazModulus.hermite_lindemann_holds`.
--
--   **Novelty.** Nothing beyond the parent node; its page gives the argument and the attribution.
-- source:
--   The statement and argument of `DiazModulus.candidate_one_log_saturation` (C. Perassi's working notes of 12 September 2026), with Baker's theorem (A. Baker, Linear forms in the logarithms of algebraic numbers I, Mathematika 13 (1966), 204–216) proved in this mission as `DiazModulus.baker_two_logs`. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

namespace DiazModulus

theorem candidate_one_log_saturation_unconditional {u : ℂ} (h : IsCandidate u) :
    (∀ l : ℂ, l ∈ LogAlg → ∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar →
        u = a + b * l → ∃ r : ℚ, u = (r : ℂ) * l)
      ∧ (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → u ≠ a + b * ((Real.pi : ℝ) : ℂ)) := by
  sorry

end DiazModulus
