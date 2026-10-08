-- Prove2me | Theorems.Thm_AffinePSD_Necessity_lemma_3_2
-- name    : AffinePSD.Necessity.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:18.562003+00:00
-- url     : https://prove2.me/theorems/21ba4ee7-88c8-4e0e-a1ed-c8fecfd2f57e
-- title:
--   Lemma 3.2 — semiflow identities, monotonicity, continuity and analyticity of $\varphi$, $\psi$
-- statement:
--   Let $X$ be an affine process on $S_d^+$ with transition family $p_t$ and exponents $\varphi, \psi$ in (2.1). Then:
--
--   1. For all $t, s \ge 0$ and $u \in S_d^+$,
--   $$\varphi(t+s,u) = \varphi(t,u) + \varphi(s, \psi(t,u)), \qquad \psi(t+s,u) = \psi(s,\psi(t,u)). \qquad (3.1),\ (3.2)$$
--   2. For all $u, v \in S_d^+$ with $v \preceq u$ and all $t \ge 0$: $\varphi(t,v) \le \varphi(t,u)$ and $\psi(t,v) \preceq \psi(t,u)$ (3.3).
--   3. $\varphi$ and $\psi$ are jointly continuous on $\mathbb R_+ \times S_d^+$, and for each $t \ge 0$ the maps $u \mapsto \varphi(t,u)$ and $u \mapsto \psi(t,u)$ are real analytic on $S_d^{++}$.
--
--   These are the structural properties of the exponents used to show that affine processes are Feller and regular.
--
--   **Formalization Note.** Since $S_d^{++}$ is open in $S_d$ but not in $M_d$, analyticity on $S_d^{++}$ is stated as analyticity of $y \mapsto \varphi(t, \mathrm{sym}\,y)$ on the open set $\{y \in M_d : \mathrm{sym}\,y \in S_d^{++}\}$, where $\mathrm{sym}\,y = (y+y^\top)/2$; this is equivalent to analyticity on $S_d^{++}$ in coordinates of $S_d$. Joint continuity is continuity on $[0,\infty) \times S_d^+$ as a subset of $\mathbb R \times M_d$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Lemma 3.2 and (3.1)–(3.3), pp. 15–16

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Process

open MeasureTheory ProbabilityTheory

namespace AffinePSD.Necessity

/-- Lemma 3.2 (arXiv:0910.0137v3, §3, pp. 15–16). Let `X` be an affine process on `S_d^+` with exponents
`φ, ψ` in (2.1). Then
(i) `φ(t+s,u) = φ(t,u) + φ(s,ψ(t,u))` (3.1) and `ψ(t+s,u) = ψ(s,ψ(t,u))` (3.2) for all `t, s ≥ 0`;
(ii) for `u, v ∈ S_d^+` with `v ⪯ u` and `t ≥ 0`: `φ(t,v) ≤ φ(t,u)` and `ψ(t,v) ⪯ ψ(t,u)` (3.3);
(iii) `φ` and `ψ` are jointly continuous on `ℝ_+ × S_d^+`, and `u ↦ φ(t,u)`, `u ↦ ψ(t,u)` are analytic
on `S_d^{++}`.

**Formalization Note.** Exponents live on `M_d` and are only constrained at `t ≥ 0` and PSD `u`.
Analyticity on `S_d^{++}` (open in `S_d`, not in `M_d`) is stated as analyticity of `y ↦ φ(t, sym y)` on
the open set `{y ∈ M_d : sym y ∈ S_d^{++}}`, with `sym y = (y + y^⊤)/2`; this is equivalent to
analyticity on `S_d^{++}` in `S_d` coordinates. -/
theorem lemma_3_2 {d : ℕ} (p : ℝ → Kernel (Cone d) (Cone d)) (φ : ℝ → Mat d → ℝ)
    (ψ : ℝ → Mat d → Mat d) (hX : IsAffineWith p φ ψ) :
    -- (i)
    (∀ t s : ℝ, 0 ≤ t → 0 ≤ s → ∀ u : Mat d, PSD u →
      φ (t + s) u = φ t u + φ s (ψ t u) ∧ ψ (t + s) u = ψ s (ψ t u)) ∧
    -- (ii)
    (∀ t : ℝ, 0 ≤ t → ∀ u v : Mat d, PSD u → PSD v → PSD (u - v) →
      φ t v ≤ φ t u ∧ PSD (ψ t u - ψ t v)) ∧
    -- (iii)
    ContinuousOn (fun q : ℝ × Mat d => φ q.1 q.2) (Set.Ici 0 ×ˢ {u | PSD u}) ∧
    ContinuousOn (fun q : ℝ × Mat d => ψ q.1 q.2) (Set.Ici 0 ×ˢ {u | PSD u}) ∧
    (∀ t : ℝ, 0 ≤ t →
      AnalyticOnNhd ℝ (fun y => φ t (sym y)) {y | PD (sym y)} ∧
      AnalyticOnNhd ℝ (fun y => ψ t (sym y)) {y | PD (sym y)}) := by sorry

end AffinePSD.Necessity
