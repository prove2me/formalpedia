-- Prove2me | Theorems.Thm_AutoregLTF_eq_46
-- name    : AutoregLTF.eq_46
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:53:28.203387+00:00
-- url     : https://prove2.me/theorems/e8609be3-a648-4381-8012-9c3c0b617c88
-- title:
--   (46), proof of Theorem 1, p.14 — $f^T_0(1,\dots,1)=0$, $f^T_{(1,0,\dots,0)}(1,\dots,1)=1$, so $\mathrm{VCdim}(\mathcal F_{d,T})\ge1$
-- statement:
--   Let $d\ge1$ and $T\ge1$. For the all-ones prompt $(1,\dots,1)\in\{0,1\}^d$, the zero weight vector and the weight vector $(1,0,\dots,0)$ (weight $1$ on the most recent bit) give
--
--   $$f^T_0(1,\dots,1)=0,\qquad f^T_{(1,0,\dots,0)}(1,\dots,1)=1,$$
--
--   so the one-point set $\{(1,\dots,1)\}$ is shattered and $\mathrm{VCdim}(\mathcal F_{d,T})\ge1$.
--
--   This is the case $m=1$ of the proof of Theorem 1, where Lemma 3 does not apply.
--
--   Differences from the source:
--   - generalization: the case m = 1 of the proof of Theorem 1 (d ≤ 1512, T ≥ d²) → every d ≥ 1 and T ≥ 1; reason: the computation from (1) uses only T ≥ 1; the m = 1 case satisfies these hypotheses
--   - encoding: VCdim(F_{d,T}) ≥ 1 → 1 ≤ QAlgorithms.Learning.vcDimSet (cls d T) in ℕ∞; reason: the published VC dimension is the paper's (p.2)
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), proof of Theorem 1, (46), p.14

import Mathlib
import Definitions.Def_QAlgorithms_Defs_PACSampleComplexity
import Definitions.Def_AutoregLTF_ltf

namespace AutoregLTF

/-- **Proof of Theorem 1, (46)**, p.14 (PDF p.14).

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e).

"If `m = 1`, (1) gives `f^T_0(1, …, 1) = 0`, `f^T_{(1,0,…,0)}(1, …, 1) = 1` (46), so
`VCdim(F_{d,T}) ≥ 1 = m²` in this case as well."

Stated for every `d ≥ 1` and `T ≥ 1`: the all-zero weights send the all-ones prompt to `0`, the weights
`(1, 0, …, 0)` (weight `1` on the most recent bit) send it to `1`, and `VCdim(F_{d,T}) ≥ 1`.

**Formalization Note.** `(1, 0, …, 0)` is `w_1 = 1`, `w_ℓ = 0` for `ℓ ≥ 2`; in Lean `w ⟨0, _⟩ = w_1`.
The VC dimension is `QAlgorithms.Learning.vcDimSet` (in `ℕ∞`). -/
theorem eq_46 (d T : ℕ) (hd : 1 ≤ d) (hT : 1 ≤ T) :
    ltf d T (fun _ => 0) (fun _ => true) = false ∧
    ltf d T (fun ℓ => if ℓ.val = 0 then 1 else 0) (fun _ => true) = true ∧
    1 ≤ QAlgorithms.Learning.vcDimSet (cls d T) := by sorry

end AutoregLTF
