-- Prove2me | Theorems.Thm_ChoiSemiHonestMPC_OTUpper_lemma_4_3
-- name    : ChoiSemiHonestMPC.OTUpper.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:29:00.966213+00:00
-- url     : https://prove2.me/theorems/1fe710c0-b3ba-4fe2-84ed-567352ceed43
-- title:
--   Lemma 4.3 — bias of a hidden half
-- statement:
--   Let $m\ge r\ge2$ with $r$ even and $0\le t\le m$, and let $C_0,C_1\subseteq\{0,\dots,m-1\}$ be disjoint halves of size $r/2$. Let $\mu_b$ be the law of $(E,Z)$, where $J$ is uniform on $C_b$ (that is, $J$ uniform on $C_0\cup C_1$ conditioned on $B=b$), $E$ is an independent uniform $t$-subset, and $Z=J$ if $J\in E$, $Z=\bot$ otherwise. Then
--   $$\mathrm{TV}(\mu_0,\mu_1)=\frac tm+\frac{\mathbb E_E|N_0-N_1|}{r}\le\frac tm+\sqrt{\frac{t(m-t)}{rm(m-1)}},\qquad N_b=|C_b\setminus E|,$$
--   with the expectation written as the average over all $\binom mt$ subsets.
--
--   Differences from the source:
--   - encoding: server labels [n] = {1,…,n}; positions and tags counted from 1 → `Fin n` = {0,…,n−1}; positions and tags counted from 0; reason: relabelling by −1 changes no instance
--   - encoding: μ_b = L(View | B = b) with J uniform on C → J uniform on the half C_b; reason: conditioning a uniform J on J ∈ C_b gives the uniform law on C_b
--   - encoding: E[|N0 − N1|] over E → the average of |N0 − N1| over the C(m, t) t-subsets; reason: E is uniform on t-subsets
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Lemma 4.3, p. 16 (PDF 18)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Sampling

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- Lemma 4.3 (bias of a hidden half). -/
theorem lemma_4_3 (m r t : ℕ) (hr2 : 2 ≤ r) (hrE : Even r) (hrm : r ≤ m) (htm : t ≤ m)
    (C0 C1 : Finset (Fin m)) (hdisj : Disjoint C0 C1)
    (hC0 : C0.card = r / 2) (hC1 : C1.card = r / 2) :
    tvPMF (hiddenHalfLaw m t C0) (hiddenHalfLaw m t C1) =
        (t : ℝ) / m +
          ((∑ E ∈ (Finset.univ : Finset (Fin m)).powersetCard t,
              |((C0 \ E).card : ℝ) - ((C1 \ E).card : ℝ)|) / (m.choose t : ℝ)) / r ∧
      tvPMF (hiddenHalfLaw m t C0) (hiddenHalfLaw m t C1) ≤
        (t : ℝ) / m + Real.sqrt ((t : ℝ) * ((m : ℝ) - t) / ((r : ℝ) * m * ((m : ℝ) - 1))) := by sorry

end ChoiSemiHonestMPC.OTUpper
