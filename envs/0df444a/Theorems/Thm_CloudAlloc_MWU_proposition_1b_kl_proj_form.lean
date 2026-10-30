-- Prove2me | Theorems.Thm_CloudAlloc_MWU_proposition_1b_kl_proj_form
-- name    : CloudAlloc.MWU.proposition_1b_kl_proj_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:39:20.315026+00:00
-- url     : https://prove2.me/theorems/91201f82-a0e5-42a6-b54d-9631b8e0369e
-- title:
--   Proposition 1(b): form of the KL projection onto $\Delta_\varepsilon$
-- statement:
--   Let $N\ge 2$ and $0<\varepsilon<1$. Let $y\in\mathbb R^N$ have positive entries, let $x=\pi_{\Delta_\varepsilon}(y)$ be its KL projection onto the truncated simplex, and let $S=\{i: x(i)=\varepsilon/N\}$ be the coordinates at the floor. Then there are numbers $\mu_i\ge 0$, with $\mu_i=0$ for $i\notin S$, such that for every $i$
--
--   $$
--   x(i)=y(i)\,e^{\mu_i}\,C,\qquad C=\frac{1-\frac{\varepsilon}{N}|S|}{\sum_{j\notin S}y(j)} .
--   $$
--
--   The projection rescales the unconstrained coordinates by a common factor and lifts the others to the floor; this is the structure used in the proofs of Lemmas 1 and 2.
--
--   Differences from the source:
--   - reading: y ∈ R^N_+ → y(i) > 0 for every i; reason: at y(i) = 0 the objective Σ x log(x/y) is +∞ for every x ∈ Δ_ε and the argmin is undefined
--   - encoding: x = π_{Δ_ε}(y), an argmin → IsKLProj N ε y x (x ∈ Δ_ε and minimizes the objective over Δ_ε); reason: argmin as a predicate, no choice function; the minimizer is unique for y > 0
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, Proposition 1(b), p. 9 (proof in Appendix A, p. 26)

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsKLProj

namespace CloudAlloc.MWU

/-- **Proposition 1(b): the form of the KL projection onto `Δ_ε`.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal
Efficiency*, arXiv:1809.02688v3, Proposition 1(b), p. 9 (proof in Appendix A, p. 26):
"Let `y ∈ R^N_+`, `x = π∆ε(y)`, and `S = {i : x(i) = ε/N}`. Then: (b) `x(i) = y(i)e^{µi}C`, where
`C = ((1 − (ε/N)|S|)/Σ_{j∉S} y(j))`, `µi ≥ 0` for all `i` and `µi = 0` for `i ∉ S`."

For `N ≥ 2` users, `0 < ε < 1`, a vector `y` with positive entries and its KL projection `x` onto
`Δ_ε`, with `S` the set of coordinates of `x` at the floor `ε/N`, there are multipliers `μ_i ≥ 0`,
vanishing off `S`, with `x(i) = y(i) e^{μ_i} C` for every `i`.

**Formalization Note.** `0 < ε < 1` is §2.1's "For `0 < ε < 1`" (p. 8) and `N ≥ 2` its standing
assumption "We assume `N ≥ 2`" (p. 8). The paper's `y ∈ R^N_+` is read as `y > 0` entrywise: at
`y(i) = 0` the objective `Σ x log(x/y)` is `+∞` for every `x ∈ Δ_ε`, and the argmin is undefined.
`x = π_{Δ_ε}(y)` is the predicate `IsKLProj N ε y x`. `j ∉ S` is `Sᶜ` in `Fin N`; it is nonempty
because `ε < 1`, so the denominator of `C` is positive. -/
theorem proposition_1b_kl_proj_form {N : ℕ} (hN : 2 ≤ N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {y x : Fin N → ℝ} (hy : ∀ i, 0 < y i) (hx : IsKLProj N ε y x) :
    let S := Finset.univ.filter (fun i => x i = ε / N)
    ∃ μ : Fin N → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i ∉ S, μ i = 0) ∧
      ∀ i, x i = y i * Real.exp (μ i) * ((1 - ε / N * S.card) / ∑ j ∈ Sᶜ, y j) := by sorry

end CloudAlloc.MWU
