-- Prove2me | Theorems.Thm_AutoregLTF_theorem_1
-- name    : AutoregLTF.theorem_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:53:34.197017+00:00
-- url     : https://prove2.me/theorems/41584f7a-6068-4168-96a5-5e874bd33462
-- title:
--   Theorem 1, p.2 — $\mathrm{VCdim}(\mathcal F_{d,T})\ge d^2/3024^2$ for all integers $d\ge1$ and $T\ge d^2$
-- statement:
--   For integers $d\ge1$ and $w\in\mathbb Q^d$, the autoregressive LTF $f^T_w:\{0,1\}^d\to\{0,1\}$ maps a prompt $x=(x_{1-d},\dots,x_0)$ to $z_T$, where $z_t=x_t$ for $1-d\le t\le0$ and $z_t=\mathbf 1\{\sum_{\ell=1}^dw_\ell z_{t-\ell}\ge1\}$ for $t\ge1$. Let $\mathcal F_{d,T}=\{f^T_w:w\in\mathbb Q^d\}$. A set $A\subseteq\{0,1\}^d$ is shattered by $\mathcal F_{d,T}$ if every $\lambda:A\to\{0,1\}$ is realized by some $f\in\mathcal F_{d,T}$, and $\mathrm{VCdim}(\mathcal F_{d,T})$ is the maximum size of a shattered set.
--
--   **Theorem 1.** For all integers $d,T\ge1$ with $T\ge d^2$,
--
--   $$\mathrm{VCdim}(\mathcal F_{d,T})\ \ge\ \frac{d^2}{3024^2}.$$
--
--   The one-step class $\mathcal F_{d,1}$ has VC dimension $d$, and counting gives $\mathrm{VCdim}(\mathcal F_{d,T})=O(d^2)$ for every $T$; Theorem 1 shows this quadratic order is attained once $T\ge d^2$, by a single fixed LTF with rational weights applied autoregressively.
--
--   **Formalization Note** The VC dimension is the published `QAlgorithms.Learning.vcDimSet`, a supremum in $\mathbb N\cup\{\infty\}$ over shattered finite sets, and the bound is stated without division as $d^2\le3024^2\cdot\mathrm{VCdim}(\mathcal F_{d,T})$.
--
--   Differences from the source:
--   - encoding: VCdim(F_{d,T}) ≥ d²/3024² → d² ≤ 3024² · vcDimSet (cls d T) in ℕ∞; reason: equivalent for an ℕ∞-valued VC dimension; no rounding
--   - encoding: d, T ≥ 1 with T ≥ d² → 1 ≤ d and d² ≤ T; reason: T ≥ 1 follows from T ≥ d² ≥ 1
--   - encoding: {0,1}^d with x = (x_{1−d}, …, x_0), w ∈ Q^d → Fin d → Bool with index k holding x_{1−d+k}; w : Fin d → ℚ with w ⟨ℓ⟩ = w_{ℓ+1}; reason: a fixed relabeling of coordinates; same class
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), Theorem 1, p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_PACSampleComplexity
import Definitions.Def_AutoregLTF_ltf

namespace AutoregLTF

/-- **Theorem 1**, p.2 (PDF p.2).

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e).

"For all integers `d, T ≥ 1` with `T ≥ d²`, `VCdim(F_{d,T}) ≥ d²/3024²`."

`F_{d,T} = {f^T_w : w ∈ ℚ^d}` is the class of autoregressive LTFs of recurrence (1): rational weights,
threshold `1`, no bias, a window of the last `d` bits, output `z_T`.

**Formalization Note.** The VC dimension is `QAlgorithms.Learning.vcDimSet` (the supremum in `ℕ∞` of
the sizes of shattered finite sets of prompts `Fin d → Bool`), and `VCdim ≥ d²/3024²` is stated without
division as `d² ≤ 3024² · VCdim` in `ℕ∞`, which is equivalent. `T ≥ 1` is implied by `T ≥ d² ≥ 1` and
is not a separate hypothesis. -/
theorem theorem_1 (d T : ℕ) (hd : 1 ≤ d) (hT : d ^ 2 ≤ T) :
    ((d ^ 2 : ℕ) : ℕ∞) ≤ 3024 ^ 2 * QAlgorithms.Learning.vcDimSet (cls d T) := by sorry

end AutoregLTF
