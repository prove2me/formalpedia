-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_claim13_vector_eml
-- name    : ExpanderWalkDecode.Main.claim13_vector_eml
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:28.545397+00:00
-- url     : https://prove2.me/theorems/12d78bcb-3816-47d2-b962-f1fb7a052d43
-- title:
--   Claim 13 — expander mixing lemma for vector inner products
-- statement:
--   Let $V$ be (the vertex set of) a $\lambda$-expander and $f,g:V\to\mathbb R^D$. With $\vec\mu_f=\mathbb E_v[f(v)]$ and $\|\vec\mu_f\|^2+\tau_f^2=\mathbb E_v\|f(v)\|^2$ (and likewise for $g$),
--   $$\Big|\mathbb E_{v\sim w}\big[\langle f(v),g(w)\rangle\big]-\langle\vec\mu_f,\vec\mu_g\rangle\Big|\le\lambda\,\tau_f\,\tau_g ,$$
--   where $v$ is uniform and $w$ is a uniform neighbour of $v$.
--
--   It is the vector form of the expander mixing lemma and is used to prove the matrix versions (Claims 6 and 15).
--
--   The expansion parameter $\lambda$ is positive, as stipulated in §3.3.
--
--   Differences from the source:
--   - encoding: E_{v∼w} → average over a uniform vertex and a uniform port of the rotation map; reason: same distribution of edges
--   - encoding: a λ-expander → a regular graph given by a rotation map with nonempty vertex and port sets; reason: excludes only the degenerate graphs where the average is undefined
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 20 (PDF p. 23), Appendix A, Claim 13

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Graphs

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Claim 13 (Appendix A, p. 20): on a `λ`-expander, for `f, g : V → ℝ^D`,
`|E_{v∼w} ⟨f(v), g(w)⟩ - ⟨μ_f, μ_g⟩| ≤ λ τ_f τ_g`, where `μ_f = E_v f(v)` and
`‖μ_f‖² + τ_f² = E_v ‖f(v)‖²`. -/
theorem claim13_vector_eml {V P : Type} [Fintype V] [Nonempty V] [Fintype P] [Nonempty P] {D : ℕ}
    (G : RotGraph V P) (lam : ℝ) (hpos : 0 < lam) (hG : G.IsExpander lam) (f g : V → Fin D → ℝ) :
    |(avg fun vi : V × P => f vi.1 ⬝ᵥ g (G.nbr vi.1 vi.2)) - avg f ⬝ᵥ avg g| ≤
      lam * Real.sqrt ((avg fun v => f v ⬝ᵥ f v) - avg f ⬝ᵥ avg f)
        * Real.sqrt ((avg fun v => g v ⬝ᵥ g v) - avg g ⬝ᵥ avg g) := by sorry

end ExpanderWalkDecode.Main
