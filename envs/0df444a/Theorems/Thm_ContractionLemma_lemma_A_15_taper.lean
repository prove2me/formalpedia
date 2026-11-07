-- Prove2me | Theorems.Thm_ContractionLemma_lemma_A_15_taper
-- name    : ContractionLemma.lemma_A_15_taper
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:01:16.850332+00:00
-- url     : https://prove2.me/theorems/f6aefd60-ccc7-470d-9172-4856af2a2146
-- title:
--   Lemma A.15 — the taper
-- statement:
--   Let $G$ be a bipartite network with $M\ge 1$ edges placed into packets of $L=2^a$ slots, with rewiring polynomial $F$. Let $1\le u\le a$ and $h=\lceil 3M/u\rceil$. Take the orders $q_i=h\max(0,u-i)$ for $i\ge 0$, and put $m_t=q_{v_2(t)}$ for $t\in\mathcal E$. Then:
--
--   1. (enough data) $\sum_{t\in\mathcal E}m_t>M(2L-1)\ge\deg F$;
--   2. (small loss) for every easy point $t$ of level $i$, $-v_2(E_t(0))\le 6hD_i$;
--   3. (equal work) for an easy point $t$ of level $i<u$ and $c>0$, if $p_t\le cMD_i/u$, then the number of surviving monomials at $t$ is at most
--   $$
--   \exp\big(3\sqrt{6c}\,M/\sqrt u\big),
--   $$
--   a bound that does not depend on $i$.
--
--   This choice of orders gains a factor $\sqrt u$ in the exponent at every level.
--
--   **Formalization Note** In part 3 the modes are all $(P,y_0,b)$ with $P$ one of at most $3M/L$ packets, $y_0<2^{i+1}$ a tile and $b+1<p_t$, of weight $b+1$, which is the list of the proof of Lemma A.12.1.
--
--   Differences from the source:
--   - reading: the setting of a call, where Lemma A.9 gives M ≥ LQ ≥ 1 → the hypothesis M ≥ 1, stated explicitly; reason: at M = 0 and u = a = 1, part (a) would read 0 > 0, and a call always has M ≥ 1
--   - reading: the surviving monomials at t, counted with Lemma A.12(a) → exponent vectors over the full list of modes (P, y₀, b) of the proof, with at most 3M/L packets as a hypothesis; reason: this is the mode list of the proof; the kept modes of Splitting.modeSet are a subset
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.15, p.73; proof p.94

import Mathlib
import Definitions.Def_ContractionLemma_kernel
import Definitions.Def_ContractionLemma_BipNet
import Definitions.Def_ContractionLemma_BipNet_Phi
import Definitions.Def_ContractionLemma_Placement
import Definitions.Def_ContractionLemma_BipNet_rewiring
import Definitions.Def_ContractionLemma_zoom
import Definitions.Def_ContractionLemma_Et

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

/-- **Lemma A.15 (The taper)** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript,
sha256 049caea1…), p.73 (PDF p.76); proof p.94.

Let `G` be a bipartite network with `M ≥ 1` edges placed into packets of `L = 2^a` slots, with
rewiring polynomial `F`. Let `1 ≤ u ≤ a` and `h = ⌈3M/u⌉`, take the orders
`q_i = h max(0, u − i)` and put `m_t = q_{v₂(t)}` for `t ∈ E`. Then:
(a) (enough data) `∑_{t∈E} m_t > M(2L − 1) ≥ deg F`;
(b) (small loss) for every easy point `t` of level `i`, `−v₂(E_t(0)) ≤ 6 h D_i`;
(c) (equal work) for an easy point `t` of level `i < u` and `c > 0`, if `p_t ≤ c M D_i/u`,
the number of surviving monomials at `t` is at most `exp(3√(6c) M/√u)`.

**Formalization Note.** `M ≥ 1` holds in the setting of a call (Lemma A.9's `M ≥ LQ`); at
`M = 0` part (a) would read `0 > 0`. In (c) the modes at `t` are counted over all tiles of all
`np ≤ 3M/L` packets: a mode is `(P, y₀, b)` with `P` a packet, `y₀ < 2^{i+1}` a tile and
`b + 1 < p_t`, of weight `b + 1` (App. A.9.2, p.89); a surviving monomial is an exponent vector
of total weight `< p_t`. This superset of the modes of Lemma A.12 gives a count at least as
large. -/
theorem lemma_A_15_taper {U W E K : Type*} [Fintype U] [Fintype W] [Fintype E] [DecidableEq E]
    [CommRing K] [Algebra ℚ K] (G : BipNet U W E K) (a u : ℕ) (pl : Placement E a)
    (hu1 : 1 ≤ u) (hua : u ≤ a) (hM : 1 ≤ Fintype.card E) :
    (Fintype.card E * (2 * 2 ^ a - 1) <
        ∑ t ∈ easyPts a, orderAt (fun i => ⌈(3 * Fintype.card E : ℚ) / u⌉₊ * (u - i)) t ∧
      (G.rewiring pl).natDegree ≤ Fintype.card E * (2 * 2 ^ a - 1)) ∧
    (∀ t ∈ easyPts a,
      -((padicValRat 2 ((Et a (fun i => ⌈(3 * Fintype.card E : ℚ) / u⌉₊ * (u - i)) t).eval 0)
          : ℤ) : ℚ) ≤
        6 * ⌈(3 * Fintype.card E : ℚ) / u⌉₊ * (2 : ℚ) ^ (a - padicValInt 2 t)) ∧
    (∀ t ∈ easyPts a, padicValInt 2 t < u → ∀ (c : ℝ), 0 < c → ∀ (np pt : ℕ),
      (np : ℝ) * 2 ^ a ≤ 3 * Fintype.card E →
      (pt : ℝ) ≤ c * Fintype.card E * 2 ^ (a - padicValInt 2 t) / u →
      {β : {ξ : Fin np × Fin (2 ^ (padicValInt 2 t + 1)) × Fin pt // ξ.2.2.1 + 1 < pt} → ℕ |
          ∑ ξ, (ξ.1.2.2.1 + 1) * β ξ < pt}.Finite ∧
      (({β : {ξ : Fin np × Fin (2 ^ (padicValInt 2 t + 1)) × Fin pt // ξ.2.2.1 + 1 < pt} → ℕ |
          ∑ ξ, (ξ.1.2.2.1 + 1) * β ξ < pt}.ncard : ℕ) : ℝ) ≤
        Real.exp (3 * Real.sqrt (6 * c) * Fintype.card E / Real.sqrt u)) := by sorry

end ContractionLemma
