-- Prove2me | Theorems.Thm_ErdosRenyiLSC_Main_lemma_7_1
-- name    : ErdosRenyiLSC.Main.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:34.40417+00:00
-- url     : https://prove2.me/theorems/4a59f5f1-41ed-4a57-a765-94781c66342b
-- title:
--   Lemma 7.1 — rank-one perturbation bound for the trace error
-- statement:
--   Let $H$ be a real symmetric $N\times N$ matrix with $N\ge1$, let $f\ge0$, and set $A=H+f|e\rangle\langle e|$. For every $z=E+i\eta$ with $\eta>0$, the errors $\Lambda(z)=|m_H(z)-m_{\mathrm{sc}}(z)|$ and $\widetilde\Lambda(z)=|m_A(z)-m_{\mathrm{sc}}(z)|$ satisfy
--
--   $$|\widetilde\Lambda(z)-\Lambda(z)|\le\frac{\pi}{N\eta}.$$
--
--   This deterministic estimate transfers normalized-trace control from the centered matrix to its rank-one deformation.
--
--   **Formalization Note** The theorem covers the whole upper half-plane, which contains the paper's $D_L$.
-- source:
--   Erdős, Knowles, Yau and Yin, Spectral statistics of Erdős–Rényi graphs I: Local semicircle law, arXiv:1103.1919v5, p. 65, Lemma 7.1

import Mathlib
import Definitions.Def_ErdosRenyiLSC_Main_Setting

noncomputable section

namespace ErdosRenyiLSC.Main

/-- Lemma 7.1, p. 65: the normalized resolvent traces differ by at most π/(Nη). -/
theorem lemma_7_1 {N : ℕ} (hN : 0 < N)
    (H : Matrix (Fin N) (Fin N) ℝ)
    (hsymm : ∀ i j : Fin N, H i j = H j i)
    (f : ℝ) (hf : 0 ≤ f) (z : ℂ) (hz : 0 < z.im) :
    |‖stieltjes (H + f • proj N) z - msc z‖ -
      ‖stieltjes H z - msc z‖| ≤
      Real.pi / ((N : ℝ) * z.im) := by sorry

end ErdosRenyiLSC.Main
