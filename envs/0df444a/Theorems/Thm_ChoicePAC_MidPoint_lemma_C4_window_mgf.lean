-- Prove2me | Theorems.Thm_ChoicePAC_MidPoint_lemma_C4_window_mgf
-- name    : ChoicePAC.MidPoint.lemma_C4_window_mgf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:28.487212+00:00
-- url     : https://prove2.me/theorems/5c789cbd-1556-46e5-a09b-7f562003c7a6
-- title:
--   Lemma C.4 — exponential moment of the one-window OPAC deviation
-- statement:
--   Consider a valid instance. There is a constant $\varphi$ such that the following holds for every $k \ge 1$, every window $[s,t)$ of length $\ell = t-s \ge 0$, every admissible allocation $p$ (with $p_j \ge 0$ and $\sum_{j\in S_q}p_j \le 1$), every $r$ with $|r\xi_{\max}| \le 1$ and every resource $i$. When OPAC is applied during $[s,t)$ with allocation probabilities $p$,
--   $$\mathbb E\Big[\exp\big(r\tilde\Delta_i(s,t)\big)\Big] \le \prod_q \exp\Big(k\lambda_q(t-s)r^2\sum_{j\in S_q}p_j\,\mathbb E[A_{ij}^2]\Big) \le \exp\big(k\varphi(t-s)r^2\big),$$
--   where $\tilde\Delta_i(s,t) = \zeta_i - \sum_j k\lambda_{q(j)}(t-s)p_j\bar A_{ij}$ is the deviation of the consumption of resource $i$ from its conditional mean.
--
--   This sub-Gaussian bound on the window deviation is the basic probabilistic estimate behind the bound on the hitting time in the proof of Theorem 5.3.
--
--   **Formalization Note** $\varphi$ is chosen before $k$, $\ell$, $p$, $r$ and $i$: the page says "independent of $i$", and the proof's $\varphi$ does not depend on the others either. The page's first equality (the definition of $\tilde\Delta$ via i.i.d. copies) is the definition of the expectation used here; conditioning on $\{p_j\}$ is the choice of a fixed $p$. The standing hypotheses (`IsValid`) are the disclosed reading of Sec. 2.1, p. 315, Sec. 2.3, p. 317 and Sec. 5.2, p. 327: printed are $\lambda_q \ge 0$, bounded nonnegative consumption and $r_j(0)=0$; read in are $C \ge 0$, consumption laws that are probability measures, $A_{ij} \le \xi_j$ almost surely (the page writes $\xi_j \ge A_{ij}$ on p. 317 and $A_{ij} < \xi_j$ on p. 327; the weaker $\le$ is used), measurable revenue functions, and revenue that is nonnegative and bounded by a common constant (implicit on the page, needed in App. C.4).
-- source:
--   Jasin, Kumar, A Re-Solving Heuristic with Bounded Revenue Loss for Network Revenue Management with Customer Choice, Math. Oper. Res. 37(2), 2012, App. C.2, p. 338, Lemma C.4

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model
import Definitions.Def_ChoicePAC_MidPoint_OPAC

namespace ChoicePAC.MidPoint
open MeasureTheory in
theorem lemma_C4_window_mgf {NT n m : ℕ} (I : Instance NT n m) (hI : I.IsValid) :
    ∃ φ : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ ℓ : ℝ, 0 ≤ ℓ → ∀ p : Fin n → ℝ, I.AdmissibleProbs p →
      ∀ r : ℝ, |r * I.ξmax| ≤ 1 → ∀ i : Fin m,
        I.opacExpect k ℓ p (fun ζ => Real.exp (r * (ζ i - I.opacMean k ℓ p i))) ≤
            ∏ q, Real.exp ((k : ℝ) * I.lam q * ℓ * r ^ 2 *
              ∑ j ∈ I.S q, p j * ∫ a, (a i) ^ 2 ∂(I.D j)) ∧
          ∏ q, Real.exp ((k : ℝ) * I.lam q * ℓ * r ^ 2 *
              ∑ j ∈ I.S q, p j * ∫ a, (a i) ^ 2 ∂(I.D j)) ≤
            Real.exp ((k : ℝ) * φ * ℓ * r ^ 2) := by sorry
end ChoicePAC.MidPoint
