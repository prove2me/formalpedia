-- Prove2me | Theorems.Thm_AutoregLTF_lemma_1
-- name    : AutoregLTF.lemma_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:53:27.844625+00:00
-- url     : https://prove2.me/theorems/2031dc3d-b5b7-4c82-af22-aebd2113112c
-- title:
--   Lemma 1, p.5 — the recursion recovers row $i$: $f^t_{\theta,i,\mathrm{out},j}=\lambda_{i,j}$ for $t\ge m+1$; rounds $0,1$ are label-free
-- statement:
--   Let $m\ge2$ and let $\lambda\in\{0,1\}^{m\times m}$ be a labeling with encoding $\theta$. Then:
--
--   1. $f^t_{\theta,i,\mathrm{out},j}=\lambda_{i,j}$ for all $i,j\in[m]$ and all $t\ge m+1$;
--   2. for every labeling $\lambda'\in\{0,1\}^{m\times m}$ with encoding $\theta'$, the states agree in the first two rounds: $f^t_{\theta,i}=f^t_{\theta',i}$ for all $i\in[m]$ and $t\in\{0,1\}$.
--
--   The first assertion says the several-LTF recursion stores row $i$ of $\lambda$ in its output bits from round $m+1$ on. The second is what makes the prompts of §4 independent of the labels.
--
--   Differences from the source:
--   - encoding: a labeling λ ∈ {0,1}^{m×m} → lab : ℕ → ℕ → Bool, read only at i, j ∈ [m]; reason: every m×m matrix extends to such a function and the statement reads only the entries in [m]×[m]; same instances
--   - encoding: f^t_{θ,i} = f^t_{θ′,i} in {0,1}^{3m+2} → equality of each of the 3m + 2 bits (row j, out j for j ∈ [m], test, ptr j for j ∈ [m + 1]); reason: the state is stored as functions on ℕ; only these bits are the paper's vector
--   - encoding: t ∈ {0, 1} → t ≤ 1 for t : ℕ; reason: same set
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), Lemma 1, p.5

import Mathlib
import Definitions.Def_AutoregLTF_state

namespace AutoregLTF

/-- **Lemma 1**, p.5 (PDF p.5).

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e).

"For every labeling `λ ∈ {0,1}^{m×m}` with encoding `θ`, we have `f^t_{θ,i,out,j} = λ_{i,j}` for all
`i, j ∈ [m]` and `t ≥ m + 1`. Moreover, for every labeling `λ′ ∈ {0,1}^{m×m}` with encoding `θ′`, we
have `f^t_{θ,i} = f^t_{θ′,i}` for all `i ∈ [m]` and `t ∈ {0, 1}`."

**Formalization Note.** `m ≥ 2` is the standing assumption of §§2–4 (p.4). Labelings are
`ℕ → ℕ → Bool` read at `i, j ∈ [m]`. The equality of states `f^t_{θ,i} = f^t_{θ′,i}` in
`{0,1}^{3m+2}` is the equality of all `3m + 2` bits: `row j`, `out j` for `j ∈ [m]`, `test`, and
`ptr j` for `j ∈ [m + 1]`. `t ∈ {0, 1}` is `t ≤ 1`. -/
theorem lemma_1 (m : ℕ) (hm : 2 ≤ m) (lab : ℕ → ℕ → Bool) :
    (∀ i ∈ Finset.Icc 1 m, ∀ j ∈ Finset.Icc 1 m, ∀ t : ℕ, m + 1 ≤ t →
      (state m (enc m lab) i t).out j = lab i j) ∧
    ∀ lab' : ℕ → ℕ → Bool, ∀ i ∈ Finset.Icc 1 m, ∀ t : ℕ, t ≤ 1 →
      (∀ j ∈ Finset.Icc 1 m,
        (state m (enc m lab) i t).row j = (state m (enc m lab') i t).row j) ∧
      (state m (enc m lab) i t).test = (state m (enc m lab') i t).test ∧
      (∀ j ∈ Finset.Icc 1 m,
        (state m (enc m lab) i t).out j = (state m (enc m lab') i t).out j) ∧
      (∀ j ∈ Finset.Icc 1 (m + 1),
        (state m (enc m lab) i t).ptr j = (state m (enc m lab') i t).ptr j) := by sorry

end AutoregLTF
