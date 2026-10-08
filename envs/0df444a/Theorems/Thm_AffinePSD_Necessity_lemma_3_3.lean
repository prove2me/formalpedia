-- Prove2me | Theorems.Thm_AffinePSD_Necessity_lemma_3_3
-- name    : AffinePSD.Necessity.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:23.673863+00:00
-- url     : https://prove2.me/theorems/114a2eca-0648-474d-8454-d8a3767c2199
-- title:
--   Lemma 3.3 — an order-preserving, continuous, analytic semiflow $\psi$ maps $S_d^{++}$ into $S_d^{++}$
-- statement:
--   Let $\psi : \mathbb R_+ \times S_d^+ \to S_d^+$ be any map such that
--
--   1. $\psi(0,u) = u$ for all $u \in S_d^+$;
--   2. $\psi(t+s,u) = \psi(s,\psi(t,u))$ for all $t,s \ge 0$ and $u \in S_d^+$;
--   3. $v \preceq u$ in $S_d^+$ implies $\psi(t,v) \preceq \psi(t,u)$ for all $t \ge 0$;
--   4. $\psi$ is jointly continuous on $\mathbb R_+ \times S_d^+$, and $u \mapsto \psi(t,u)$ is real analytic on $S_d^{++}$ for each $t \ge 0$.
--
--   Then
--   $$\psi(t,u) \in S_d^{++} \qquad \text{for all } (t,u) \in \mathbb R_+ \times S_d^{++}.$$
--
--   No process appears: this is a statement about semiflows on the cone. It is the key positivity property behind the Feller property (Proposition 3.4) and is reused for the existence half of the characterization.
--
--   **Formalization Note.** $\psi$ is a function on $\mathbb R \times M_d$, constrained only at $t \ge 0$ and positive semidefinite arguments. Analyticity on $S_d^{++}$ is analyticity of $y \mapsto \psi(t, (y+y^\top)/2)$ on the open set of $y \in M_d$ whose symmetric part is positive definite.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Lemma 3.3, p. 16

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Cone

namespace AffinePSD.Necessity

/-- Lemma 3.3 (arXiv:0910.0137v3, §3, p. 16). Let `ψ : ℝ_+ × S_d^+ → S_d^+` be any map with
`ψ(0,u) = u` satisfying the `ψ`-parts of Lemma 3.2 (i)–(iii): the semiflow property (3.2), order
preservation (3.3), joint continuity on `ℝ_+ × S_d^+` and analyticity of `u ↦ ψ(t,u)` on `S_d^{++}`.
Then `ψ(t,u) ∈ S_d^{++}` for all `(t,u) ∈ ℝ_+ × S_d^{++}`.

**Formalization Note.** `ψ` is a function on `ℝ × M_d`, constrained only at `t ≥ 0` and PSD `u`.
Analyticity on `S_d^{++}` is analyticity of `y ↦ ψ(t, sym y)` on the open set `{y : sym y ∈ S_d^{++}}`
of `M_d`. No process appears. -/
theorem lemma_3_3 {d : ℕ} (ψ : ℝ → Mat d → Mat d)
    (hmaps : ∀ t : ℝ, 0 ≤ t → ∀ u : Mat d, PSD u → PSD (ψ t u))
    (h0 : ∀ u : Mat d, PSD u → ψ 0 u = u)
    (hflow : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → ∀ u : Mat d, PSD u → ψ (t + s) u = ψ s (ψ t u))
    (hmono : ∀ t : ℝ, 0 ≤ t → ∀ u v : Mat d, PSD u → PSD v → PSD (u - v) →
      PSD (ψ t u - ψ t v))
    (hcont : ContinuousOn (fun q : ℝ × Mat d => ψ q.1 q.2) (Set.Ici 0 ×ˢ {u | PSD u}))
    (hanal : ∀ t : ℝ, 0 ≤ t → AnalyticOnNhd ℝ (fun y => ψ t (sym y)) {y | PD (sym y)}) :
    ∀ t : ℝ, 0 ≤ t → ∀ u : Mat d, PD u → PD (ψ t u) := by sorry

end AffinePSD.Necessity
