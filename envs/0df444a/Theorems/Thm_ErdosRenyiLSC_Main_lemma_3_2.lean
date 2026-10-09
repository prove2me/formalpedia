-- Prove2me | Theorems.Thm_ErdosRenyiLSC_Main_lemma_3_2
-- name    : ErdosRenyiLSC.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:41.790596+00:00
-- url     : https://prove2.me/theorems/66e46efe-6ae2-4c90-918c-835fe7a83f87
-- title:
--   Lemma 3.2 — semicircle transform estimates
-- statement:
--   Let $\Sigma\ge3$ and let $z=E+i\eta$ lie in $D$, so $|E|\le\Sigma$ and $0<\eta\le3$. Write $\kappa_E=\bigl||E|-2\bigr|$. There is a constant $C>0$ depending only on $\Sigma$ such that
--
--   $$|m_{\mathrm{sc}}(z)|\asymp1,\qquad |1-m_{\mathrm{sc}}(z)^2|\asymp\sqrt{\kappa_E+\eta},$$
--
--   and $\operatorname{Im}m_{\mathrm{sc}}(z)\asymp\sqrt{\kappa_E+\eta}$ when $|E|\le2$, while $\operatorname{Im}m_{\mathrm{sc}}(z)\asymp\eta/\sqrt{\kappa_E+\eta}$ when $|E|\ge2$. Here $a\asymp b$ means that $b$ is between $a/C$ and $Ca$.
--
--   These comparisons quantify the behavior of the deterministic reference transform near the spectral edges.
--
--   **Formalization Note** The stated bounds use $D$ in place of the paper's $D_L$. The same positive constant controls all four comparisons, and $D_L\subseteq D$ for the relevant large $N$.
-- source:
--   Erdős, Knowles, Yau and Yin, Spectral statistics of Erdős–Rényi graphs I: Local semicircle law, arXiv:1103.1919v5, p. 15, Lemma 3.2 (3.8)

import Mathlib
import Definitions.Def_ErdosRenyiLSC_Main_Setting

noncomputable section

namespace ErdosRenyiLSC.Main

/-- Lemma 3.2, p. 15: the comparison estimates for the semicircle transform. -/
theorem lemma_3_2 (Sigma : ℝ) (hSigma : 3 ≤ Sigma) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ domD Sigma,
      1 / C ≤ ‖msc z‖ ∧ ‖msc z‖ ≤ C ∧
      (1 / C) * Real.sqrt (kappa z.re + z.im) ≤
        ‖(1 : ℂ) - msc z ^ 2‖ ∧
      ‖(1 : ℂ) - msc z ^ 2‖ ≤
        C * Real.sqrt (kappa z.re + z.im) ∧
      (|z.re| ≤ 2 →
        (1 / C) * Real.sqrt (kappa z.re + z.im) ≤ (msc z).im ∧
        (msc z).im ≤ C * Real.sqrt (kappa z.re + z.im)) ∧
      (2 ≤ |z.re| →
        (1 / C) * (z.im / Real.sqrt (kappa z.re + z.im)) ≤ (msc z).im ∧
        (msc z).im ≤ C * (z.im / Real.sqrt (kappa z.re + z.im))) := by sorry

end ErdosRenyiLSC.Main
