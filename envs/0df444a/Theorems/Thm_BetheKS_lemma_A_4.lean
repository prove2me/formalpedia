-- Prove2me | Theorems.Thm_BetheKS_lemma_A_4
-- name    : BetheKS.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:38.75403+00:00
-- url     : https://prove2.me/theorems/a4fd809b-4bc3-401d-b2af-46b0d2cf85ca
-- title:
--   Lemma A.4 — $\Gamma_\delta$ is strictly decreasing in $\delta$ and $\Gamma_\delta\uparrow1/t$ as $\delta\downarrow0$
-- statement:
--   Fix $t\ge\sqrt d>1$ and let $\Gamma_\delta(T)=\Gamma_o$ be the root cavity weight on $T\sim\nu$. Then $\Gamma_\delta$ is strictly decreasing in $\delta$, and
--   $$
--   \Gamma_\delta\uparrow\frac1t\qquad\text{as }\delta\downarrow0,\ \text{almost surely}.
--   $$
--
--   Differences from the source:
--
--   - encoding: Ω the locally finite rooted trees, ν the Poi(d) Galton–Watson law → offspring functions on Ulam–Harris words (children ordered) with i.i.d. Poi(d) coordinates; reason: the tree read off has law ν and, given the root degree, the forward subtrees are i.i.d. ν, which is all the arguments use; κ, h, δ(μ) are unchanged
--   - encoding: Γ_δ strictly decreasing in δ → ν-a.s., simultaneously for all 0 < δ₁ < δ₂, Γ_{δ₂}(T) < Γ_{δ₁}(T); reason: the paper's identities on Ω hold with probability 1; the monotone limit is the right limit δ → 0⁺
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Lemma A.4, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_BetheKS_GWTree

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace BetheKS

/-- **Lemma A.4** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.14
(PDF p.15): `Γ_δ` is strictly decreasing in `δ`. Moreover `Γ_δ ↑ 1/t` as `δ ↓ 0`, almost surely.

Here `Γ_δ(T) = Γ_o` is the cavity weight at the root (Definition A.1); standing assumptions
`t ≥ √d > 1`.

**Formalization Note.** Strict decrease is stated `ν`-a.s., simultaneously for all pairs
`0 < δ₁ < δ₂`; the increase to `1/t` is the right limit `δ → 0⁺`, `ν`-a.s. -/
theorem lemma_A_4 (d t : ℝ) (hd : 1 < d) (ht : Real.sqrt d ≤ t) :
    (∀ᵐ K ∂gwLaw d, ∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ < δ₂ → treeGamma t δ₂ K < treeGamma t δ₁ K) ∧
    (∀ᵐ K ∂gwLaw d, Tendsto (fun δ => treeGamma t δ K) (𝓝[>] 0) (𝓝 (1 / t))) := by sorry

end BetheKS
