-- Prove2me | Theorems.Thm_ForgetAlt_lemma_3_7
-- name    : ForgetAlt.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:26:29.915908+00:00
-- url     : https://prove2.me/theorems/4da91772-d664-4b2b-a054-7c8572e1a92e
-- title:
--   Lemma 3.7: shortest paths $P_T(x,\theta)$ with (R1)–(R4); PathConstruction returns suffixes in linear time
-- statement:
--   Let $T$ be any ABT and fix the MIEs $e^*_T(x)$ arbitrarily. Then one can choose a shortest $\theta$-alternating path $P_T(x,\theta)$ from $f$ to $x$ for every $x$ and $\theta$ with $\mathrm{dist}^\theta(x)<\infty$ such that:
--
--   1. **(R1)** if $\theta=\alpha(x)$, every non-tree edge $e'$ of $P_T(x,\theta)$ has $\mathrm{vlevel}(e')<2\,\mathrm{dist}^\alpha(x)$;
--   2. **(R2)** if $\theta=\beta(x)$, every non-tree edge $e'$ of $P_T(x,\theta)$ has $\mathrm{level}(e')\le\mathrm{level}(e^*_T(x))$;
--   3. **(R3)** for every finite-volume non-tree edge $e$ incident to $x$ with $\theta=\rho(e)$, $\mathrm{level}_T(P_T(x,\theta))<\mathrm{level}(e)$, and if also $e\notin E^+_H(x)$ then $\mathrm{vlevel}_T(P_T(x,\theta))<\mathrm{vlevel}(e)$;
--   4. **(R4)** for every vertex $s$ of $P_T(x,\theta)$ such that the suffix $P_T(x,\theta)[s,x]$ lies in $T(s)$, the call $\textsc{PathConstruction}(T,s,x,\theta,e^*_T(x))$ returns this suffix in time $O(|P_T(x,\theta)[s,x]|)$.
--
--   This is the reconstruction lemma behind every augmenting path the reduction outputs.
--
--   Differences from the source:
--   - encoding: an arbitrary finite graph G → a graph on the vertex set Fin n; reason: every finite graph is isomorphic to one on Fin n; the machine part needs numbered vertices
--   - reading: the call … returns this suffix in O(|P_T(x, θ)[s, x]|) time → there is one program of the published word RAM EndStatement (constants b, C) whose step count on the stated input layout is at most C·(bound + 1), at every word width W ≥ b·(⌊log₂ size⌋ + 1); reason: the paper's time bounds are word-RAM bounds with O(log n)-bit words; the + 1 only matters when the bound is 0
--   - encoding: the call returns the suffix → PCReturns: the fuelled recursion returns it for all large enough fuel; reason: Lean functions must terminate; the fuel is never the binding constraint once large
--   - encoding: the input of the call → the ABT data (parent, α, oriented MIE, ρ of the MIE per vertex) and the call's arguments (pcInput layout); reason: the procedure reads exactly these
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Lemma 3.7, printed pp.20–21 (PDF pp.21–22)

import Mathlib
import Definitions.Def_ForgetAlt_Layouts

namespace ForgetAlt

open BergeMatching.Core

/-- **Lemma 3.7** (Shortest paths and reconstruction), printed pp.20–21 (PDF pp.21–22).
Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…).

"Let `T` be any ABT, and fix the MIEs `e*_T(x)` arbitrarily. Then one can choose a shortest
`θ`-alternating path `P_T(x, θ)` from `f` to `x` for every `x ∈ V(T)` and every `θ` with
`dist^θ(x) < ∞`, such that the following properties hold: (R1) If `θ = α(x)`, every non-tree
edge `e′` of `P_T(x, θ)` satisfies `vlevel(e′) < 2dist^α(x)`. (R2) If `θ = β(x)`, every non-tree
edge `e′` of `P_T(x, θ)` satisfies `level(e′) ≤ level(e*_T(x))`. (R3) For every finite-volume
non-tree edge `e` incident to `x` with `θ = ρ(e)`, we have `level_T(P_T(x, θ)) < level(e)`. If
also `e ∉ E⁺_H(x)`, then `vlevel_T(P_T(x, θ)) < vlevel(e)`. (R4) For any vertex `s` of
`P_T(x, θ)` such that `P_T(x, θ)[s, x]` lies in `T(s)`, the call
`PathConstruction(T, s, x, θ, e*_T(x))` returns this suffix in `O(|P_T(x, θ)[s, x]|)` time."

**Formalization Note.** The graph has vertex set `Fin n` (every finite graph is isomorphic to
one). One word-RAM program `prog` and constants `b, C` serve every graph, ABT and MIE choice:
(R4)'s time is the step count of `prog` on the `pcInput` layout (the ABT data and the call's
arguments), at most `C·(|P_T(x, θ)[s, x]| + 1)` (the `+ 1` covers `s = x`). "Returns" is
`PCReturns` (large enough fuel). `P_T(x, θ)` is a walk from `f`, chosen for each `(x, θ)` with
`dist^θ(x) < ∞`. -/
theorem lemma_3_7 :
    ∃ (prog : List EndStatement.Instr) (b C : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n))
      (M : G.Subgraph), M.IsMatching →
      ∀ par : ExtV (Fin n) → ExtV (Fin n), IsABT G M par →
      ∀ mie : ExtV (Fin n) → Sym2 (ExtV (Fin n)), MIEChoice G M par mie →
      ∃ PT : ∀ (x : ExtV (Fin n)) (θ : Parity), dist G M θ x < ⊤ → (extGraph G M).Walk .f x,
        ∀ (x : ExtV (Fin n)) (θ : Parity) (h : dist G M θ x < ⊤),
          (IsAltPath (extMatching G M) (PT x θ h) ∧ parityOf (PT x θ h).length = θ ∧
            ((PT x θ h).length : ℕ∞) = dist G M θ x) ∧
          (θ = alpha G M x → ∀ e' ∈ (PT x θ h).edges, ¬ IsTreeEdge G M par e' →
            vlevelE G M e' < 2 * distA G M x) ∧
          (θ = beta G M x → ∀ e' ∈ (PT x θ h).edges, ¬ IsTreeEdge G M par e' →
            level G M e' ≤ level G M (mie x)) ∧
          (∀ e ∈ (extGraph G M).edgeSet, x ∈ e → ¬ IsTreeEdge G M par e → vlevelE G M e < ⊤ →
            θ = rho G M e →
              levelT G M par (PT x θ h) < level G M e ∧
              (e ∉ EplusH G M x → vlevelT G M par (PT x θ h) < vlevelE G M e)) ∧
          (∀ (s : ExtV (Fin n)) (hs : s ∈ (PT x θ h).support),
            (∀ w ∈ ((PT x θ h).dropUntil s hs).support, InSubtree G M par s w) →
              PCReturns G M par mie s x θ (mie x) ((PT x θ h).dropUntil s hs).support ∧
              ∀ W : ℕ, b * (Nat.log2 (n + 2) + 1) ≤ W →
                ∃ t ≤ C * (((PT x θ h).dropUntil s hs).length + 1),
                  RunOutputs prog W t n (pcInput G M par mie s x θ (mie x))
                    (fun out => Decodes out (encExtPath ((PT x θ h).dropUntil s hs).support))) := by sorry

end ForgetAlt
