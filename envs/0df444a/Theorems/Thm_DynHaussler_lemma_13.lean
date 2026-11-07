-- Prove2me | Theorems.Thm_DynHaussler_lemma_13
-- name    : DynHaussler.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:39:02.442737+00:00
-- url     : https://prove2.me/theorems/6442ccbb-5406-45ad-b678-aad4a0901065
-- title:
--   Lemma 13 — pointwise schedule cover by at most $Q_r(m)$ causal experts
-- statement:
--   Let $\eta>0$, let $\emptyset\neq V_0\subseteq[0,1]^X$ satisfy $\mathrm{sfat}_\eta(V_0)\le r$, and let $m$ be a positive integer. Consider the simulations of the correction schedules of depth at most $r$ with ordinals in $[m]$ (Section 4.2). Then:
--
--   1. the formal family of these schedules has at most $Q_r(m)$ members;
--   2. on any instance sequence $x_1,\dots,x_n$ and any selection history with at most $m$ selected rounds, for every target $f\in V_0$ some schedule $J$ of the family has final prediction $y^J_t$ with $|y^J_t-f(x_t)|\le\eta$ at every selected round $t$;
--   3. with every round selected, for every horizon $n\le m$ the simulations are deterministic causal experts $g_J$ with values in $[0,1]$, and on every instance sequence of length $n$ each target $f\in V_0$ is approximated by one of them with pointwise error at most $\eta$.
--
--   Part 3 is the paper's first sentence (the all-round cover), part 2 its second sentence. The family is fixed independently of the target and of the sequence; this is the deterministic core of the proof of Proposition 2.
--
--   **Formalization Note** The prediction of schedule $J$ at round $t$ is the simulation `schedPred` evaluated at the list of the preceding pairs $(x_s,\text{selected}_s)$, the current instance and the current selection bit; rounds are 0-based, and the family is counted by its extended cardinality.
--
--   Differences from the source:
--   - generalization: the scale η of Section 4 satisfies 0 < η < 1 (fixed with the hypotheses of Proposition 2) → only 0 < η is assumed; reason: the proof never uses η < 1; every instance with η < 1 is an instance of the Lean statement
--   - encoding: schedules as lists ((s_1, σ_1), …), the simulation of Section 4.2 → List (ℕ × Bool) and the function schedPred on the history list, 0-based rounds; reason: the simulation is the paper's, written as a fold over rounds
--   - reading: "on every instance sequence of length at most m" with experts at a horizon → for each horizon n ≤ m, experts at horizon n covering every sequence of length n; reason: a causal expert has a fixed horizon; each sequence of length at most m is covered at its own length
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 13, p.20 (PDF p.22); schedules (34) and their simulation, pp.19–20 (PDF pp.21–22); counts (35), p.20

import Mathlib
import Definitions.Def_DynHaussler_schedPred
import Definitions.Def_DynHaussler_schedules
import Definitions.Def_DynHaussler_QCount
import Definitions.Def_DynHaussler_CausalExpert

set_option autoImplicit false

namespace DynHaussler

/-- **Lemma 13 (Pointwise schedule cover).** Let `∅ ≠ V_0 ⊆ [0,1]^X` satisfy `sfat_η(V_0) ≤ r`, and
let `m` be a positive integer. With every round selected, the schedules of depth at most `r` form
one family of at most `Q_r(m)` deterministic causal experts such that, on every instance sequence
of length at most `m`, each target in `V_0` is approximated by one expert with pointwise error at
most `η`. More generally, on any selection history with at most `m` selected rounds, a schedule in
the same formal family attains error at most `η` on every selected round.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 13, p.20 (PDF p.22); schedules (34) and their simulation, Section 4.2, pp.19–20
(PDF pp.21–22); the counts (35), p.20.

The statement has three parts: (a) the formal family `schedules m r` has at most `Q_r(m)` members;
(b) the second sentence: for every instance sequence `x` of any length `n`, every selection history
`sel` with at most `m` selected rounds and every `f ∈ V_0`, some schedule `J` in the family has
final prediction within `η` of `f(x_t)` at every selected round `t`; (c) the first sentence: for
every horizon `n ≤ m`, with every round selected, the simulations of the schedules are
deterministic causal experts `G J` (with values in `[0,1]`), and on every instance sequence of
length `n` each `f ∈ V_0` is within `η` of one of them at every round.

**Formalization Note** The prediction of schedule `J` at round `t` is
`schedPred η V₀ J h_{<t} x_t sel_t`, where `h_{<t}` is the list of the preceding pairs
`(x_s, sel_s)`; since the simulation reads only the past, the current instance and the current
selection bit, it is causal by construction, and (c) is the specialization of (b) to the
all-selected history together with the fact that the simulated predictions lie in `[0,1]`. Rounds
are 0-based. The family is counted with `Set.encard` (no junk value for infinite sets). Section 4.1
also has `η < 1`; it is not assumed here. -/
theorem lemma_13 {X : Type*} [Nonempty X] (η : ℝ) (hη : 0 < η) (V₀ : Set (X → ℝ))
    (hV₀ : V₀.Nonempty) (hV₀01 : ∀ f ∈ V₀, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (r : ℕ)
    (hr : NondualOpt.sfat V₀ η ≤ r) (m : ℕ) (hm : 0 < m) :
    (schedules m r).encard ≤ (QCount r m : ℕ∞) ∧
    (∀ (n : ℕ) (x : Fin n → X) (sel : Fin n → Bool),
      (Finset.univ.filter (fun t => sel t = true)).card ≤ m →
      ∀ f ∈ V₀, ∃ J ∈ schedules m r, ∀ t : Fin n, sel t = true →
        |schedPred η V₀ J
            (List.ofFn (NondualOpt.histPrefix (fun s => (x s, sel s)) t)) (x t) true
          - f (x t)| ≤ η) ∧
    (∀ n : ℕ, n ≤ m → ∃ G : schedules m r → CausalExpert X n,
      (∀ (J : schedules m r) (x : Fin n → X) (t : Fin n),
        (G J).run x t = schedPred η V₀ J
          (List.ofFn (NondualOpt.histPrefix (fun s => (x s, true)) t)) (x t) true) ∧
      (∀ x : Fin n → X, ∀ f ∈ V₀, ∃ J : schedules m r, ∀ t : Fin n,
        |(G J).run x t - f (x t)| ≤ η)) := by sorry

end DynHaussler
