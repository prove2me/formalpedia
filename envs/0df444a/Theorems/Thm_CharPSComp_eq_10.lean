-- Prove2me | Theorems.Thm_CharPSComp_eq_10
-- name    : CharPSComp.eq_10
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T13:08:44.435804+00:00
-- url     : https://prove2.me/theorems/d2e467d0-773e-424c-a766-71ad33779db4
-- title:
--   (10) — the integer form of Schönhage's identity $\sum_{\lambda\in\Lambda}\phi_\lambda\psi_\lambda\chi_\lambda=G+G_{\mathrm{err}}$
-- statement:
--   For every $q_0$, in the polynomial ring over $\mathbb Z$ in the variables $I_X\cup I_Y\cup I_Z$,
--   $$\sum_{\lambda\in\Lambda}\phi_\lambda\psi_\lambda\chi_\lambda=G+G_{\mathrm{err}},$$
--   where $\Lambda=\{0\}\cup[q_0]^2$, the linear forms are those of `schonhageSum`, $G=\sum_{i,j=1}^{q_0}x_iy_jz_{ij}+z_0\sum_{i,j=1}^{q_0-1}u_{ij}v_{ij}$ and $G_{\mathrm{err}}=\sum_{i,j=1}^{q_0}(x_i\widehat V_{ij}+\widehat U_{ij}y_j+\widehat U_{ij}\widehat V_{ij})z_{ij}$.
--
--   The tensor powers of this identity, restricted to the terms that avoid $G_{\mathrm{err}}$, give the batch program behind Lemma 5.
--
--   **Formalization Note** Indices are $0$-based, with the appended row and column of $\widehat U,\widehat V$ at index $q_0-1$.
--
--   Differences from the source:
--   - generalization: an outer product of side $q_0\ge4$ → every $q_0\in\mathbb N$; reason: the identity is a polynomial identity valid for every $q_0$ (the page cites the case $q_0=3$); $q_0\ge4$ is an instance
--   - encoding: indices in $[q_0]=\{1,\dots,q_0\}$, appended row/column at $q_0$ → `Fin q₀`, appended row/column at index $q_0-1$; reason: a relabelling
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), Appendix A.1, display (10), p.19 (PDF p.20)

import Mathlib
import Definitions.Def_CharPSComp_schonhageSum

namespace CharPSComp

/-- Identity (10) of Zhu, *Faster Power Series Composition in Fixed Positive Characteristic*, STOC
2027 submission (manuscript sha256 e63e0527…), Appendix A.1, p.19 (PDF p.20): the integer form of
Schönhage's identity,
`Σ_{λ∈Λ} ϕ_λ ψ_λ χ_λ = G + G_err`,
with `G ≜ Σ_{i,j=1}^{q₀} x_i y_j z_ij + z₀ Σ_{i,j=1}^{q₀−1} u_ij v_ij` and
`G_err ≜ Σ_{i,j=1}^{q₀} (x_i V̂_ij + Û_ij y_j + Û_ij V̂_ij) z_ij`, an identity in
`ℤ[I_X ∪ I_Y ∪ I_Z]`.

**Formalization Note** Stated for every `q₀`; the paper uses it for `q₀ ≥ 4` (and cites the case
`q₀ = 3`). Indices are `0`-based (`Def_CharPSComp_schonhageSum`). -/
theorem eq_10 (q : ℕ) : schonhageSum q = schonhageG q + schonhageGerr q := by sorry

end CharPSComp
