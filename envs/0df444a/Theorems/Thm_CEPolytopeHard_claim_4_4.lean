-- Prove2me | Theorems.Thm_CEPolytopeHard_claim_4_4
-- name    : CEPolytopeHard.claim_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:18:45.881864+00:00
-- url     : https://prove2.me/theorems/99183b34-8a49-4862-bd60-c99fbe4739e7
-- title:
--   Claim 4.4 — the $x$-marginal of an $\varepsilon$-CE of the constructed game is an $\eta$-convex EFP of $g$
-- statement:
--   Let the coordinates form a finite nonempty set of size $D$, let $m \in \mathbb N$, $q \ge 1$ and $M \ge 1$, let $g$ map $[0,1]^D$ into itself, and let $\tilde g$ map $q$ copies in $[0,1]^D$ into $[0,1]^D$ and satisfy (14) relative to $g$. In the constructed game (players $x$, $y$ and $q$ copies, strategy set $S$ = product of copies of the polytope (13), utilities $u_x, u_y, u_j$ of p.23), let $\mu$ be an $\varepsilon$-correlated equilibrium and
--   $$
--   \rho = \sqrt{\varepsilon + 4^{-(m+1)}}, \qquad \eta = 2(1 + qM)\rho + 3q\sqrt{M^{-1} + (2q+1)\rho}. \tag{15}
--   $$
--   Then the $x$-marginal of $\mu$ (the law of $x(s_x)$) is an $\eta$-convex expected fixed point of $g$ on $[0,1]^D$.
--
--   Together with Claim 4.2 and the parameter choice (18) this turns every small-support correlated equilibrium into an approximate fixed point of the circuit map.
--
--   Differences from the source:
--   - generalization: g the lift of the circuit map and g̃ its copy map, D = dr → any g mapping [0, 1]^D into itself and any g̃ with values in [0, 1]^D satisfying (14) relative to g, on any finite nonempty coordinate set; reason: the proof uses only these properties; eq_14 supplies them for the printed g, g̃
--   - encoding: players x, y, 1, …, q; lifted strategies (x, t, w_1, …, w_m); ϵ ≥ 0 → players none, some none, some (some j); strategies carry w_0 = x as a coordinate; any real ε; reason: Lean representation; for ε < 0 there is no ε-CE (the identity deviation gains 0)
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Claim 4.4 and Eq. (15), p.23 (construction pp.22–23)

import Mathlib
import Definitions.Def_CEPolytopeHard_nnorm
import Definitions.Def_CEPolytopeHard_IsApproxCE
import Definitions.Def_CEPolytopeHard_IsConvexEFP
import Definitions.Def_CEPolytopeHard_liftedGame

set_option autoImplicit false

namespace CEPolytopeHard

/-- **Claim 4.4 (correlated equilibria of the constructed game give convex EFPs)** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, Claim 4.4,
p.23: "Let μ be an ϵ-correlated equilibrium of the constructed game and ρ = √(ϵ + 4^{−(m+1)}). The
x-marginal of μ is an η-convex EFP of g, where η = 2(1 + qM)ρ + 3q√(M^{−1} + (2q + 1)ρ). (15)").

Let `ι` be a finite nonempty set of `D` coordinates, `m ∈ ℕ`, `q ≥ 1`, `M ≥ 1`, `g` a map of
`[0, 1]^ι` into itself and `g̃` a map of `q` copies in `[0, 1]^ι` into `[0, 1]^ι` satisfying (14)
relative to `g`. Consider the game of pp.22–23 with players `x`, `y` and `q` copy players, each
with strategy set `S` (the product over the coordinates of the polytope (13)) and the utilities
of p.23. For every `ε` and every `ε`-correlated equilibrium `μ` (deviations: all maps `S → S`), the
`x`-marginal of `μ` (the law of `x(s_x)`) is an `η`-convex EFP of `g` on `[0, 1]^ι`, with `ρ` and `η`
as in (15).

**Formalization Note** The paper's `g`, `g̃` are the lift and copy map of the circuit (`D = dr`, and
`eq_14` gives (14)); here they are any maps with the properties the proof uses, and `D = card ι`
replaces `dr`. The game is unscaled (utilities in `[−1, 2]`), as in the claim. Norms are normalized
(p.9). -/
theorem claim_4_4 {ι : Type} [Fintype ι] [Nonempty ι] (m q : ℕ) (hq : 1 ≤ q) (M : ℝ) (hM : 1 ≤ M)
    (g : (ι → ℝ) → ι → ℝ) (hg : ∀ x ∈ Set.Icc (0 : ι → ℝ) 1, g x ∈ Set.Icc (0 : ι → ℝ) 1)
    (gt : (Fin q → ι → ℝ) → ι → ℝ)
    (hgt : ∀ z : Fin q → ι → ℝ, (∀ j, z j ∈ Set.Icc (0 : ι → ℝ) 1) → gt z ∈ Set.Icc (0 : ι → ℝ) 1)
    (h14 : ∀ (z : Fin q → ι → ℝ) (x : ι → ℝ), (∀ j, z j ∈ Set.Icc (0 : ι → ℝ) 1) →
      x ∈ Set.Icc (0 : ι → ℝ) 1 →
        nnorm (gt z - g x) ≤ 3 * q * Real.sqrt (∑ j, nnorm (z j - x) ^ 2))
    (ε : ℝ) (μ : (Role q → LStrat ι m) →₀ ℝ)
    (hμ : IsApproxCE (E := fun _ : Role q => LStrat ι m) (fun _ => LStratSet ι m)
      (gameUtility m q M gt) ε μ) :
    IsConvexEFP (Set.Icc (0 : ι → ℝ) 1) g
      (2 * (1 + q * M) * Real.sqrt (ε + (4 : ℝ) ^ (-((m : ℤ) + 1))) +
        3 * q * Real.sqrt (M⁻¹ + (2 * q + 1) * Real.sqrt (ε + (4 : ℝ) ^ (-((m : ℤ) + 1)))))
      (μ.mapDomain fun s => projX (s none)) := by sorry

end CEPolytopeHard
