-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_claim6_matrix_eml
-- name    : ExpanderWalkDecode.Main.claim6_matrix_eml
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:37.834207+00:00
-- url     : https://prove2.me/theorems/a784722a-4ba2-4822-9c7b-a0dbb6be595d
-- title:
--   Claim 6 — matrix expander mixing lemma with operator variance
-- statement:
--   Let $V$ be (the vertex set of) a $\lambda$-expander and $f,g:V\to\mathbb R^{D\times D}$. With $M_f=\mathbb E_v[f(v)]$ and $\sigma_f^2=\|\mathbb E_v[f(v)^{\mathsf T}f(v)]-M_f^{\mathsf T}M_f\|_{\mathrm{op}}$ (and likewise for $g$),
--   $$\Big\|\mathbb E_{v\sim w}\big[f(v)^{\mathsf T}g(w)\big]-M_f^{\mathsf T}M_g\Big\|_{\mathrm{op}}\le\lambda\,\sigma_f\,\sigma_g .$$
--   No symmetry or orthogonality of $f,g$ is assumed.
--
--   This is the basic tool of the operator-amplification argument.
--
--   The expansion parameter $\lambda$ is positive, as stipulated in §3.3.
--
--   Differences from the source:
--   - encoding: E_{v∼w} → average over a uniform vertex and a uniform port of the rotation map; reason: same distribution of edges
--   - encoding: a λ-expander → a regular graph given by a rotation map with nonempty vertex and port sets; reason: excludes only the degenerate graphs where the average is undefined
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 10 (PDF p. 13), §3.3, Claim 6; restated p. 20 (PDF p. 23)

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Graphs

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Claim 6 (Matrix EML) (§3.3, p. 10): on a `λ`-expander, for `f, g : V → ℝ^{D×D}`,
`‖E_{v∼w}[f(v)ᵀ g(w)] - M_fᵀ M_g‖_op ≤ λ σ_f σ_g`, where `M_f = E_v f(v)` and
`σ_f² = ‖E_v[f(v)ᵀ f(v)] - M_fᵀ M_f‖_op`. -/
theorem claim6_matrix_eml {V P : Type} [Fintype V] [Nonempty V] [Fintype P] [Nonempty P] {D : ℕ}
    (G : RotGraph V P) (lam : ℝ) (hpos : 0 < lam) (hG : G.IsExpander lam) (f g : V → Matrix (Fin D) (Fin D) ℝ) :
    opNorm ((avg fun vi : V × P => (f vi.1)ᵀ * g (G.nbr vi.1 vi.2)) - (avg f)ᵀ * avg g) ≤
      lam * Real.sqrt (opNorm ((avg fun v => (f v)ᵀ * f v) - (avg f)ᵀ * avg f))
        * Real.sqrt (opNorm ((avg fun v => (g v)ᵀ * g v) - (avg g)ᵀ * avg g)) := by sorry

end ExpanderWalkDecode.Main
