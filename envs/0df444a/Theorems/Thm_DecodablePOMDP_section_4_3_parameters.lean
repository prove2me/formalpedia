-- Prove2me | Theorems.Thm_DecodablePOMDP_section_4_3_parameters
-- name    : DecodablePOMDP.section_4_3_parameters
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:27.547162+00:00
-- url     : https://prove2.me/theorems/8ff8cccf-4ebf-45c5-812b-a729d77a20d8
-- title:
--   §4.3, p.12, (8)–(9) — error $\varepsilon/2$ and $\sum_h|\mathcal M_h|\le(CAOSH/\varepsilon)^{3(L+1)}$
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $\mathcal P$ be a valid POMDP with a nonempty action set, $\rho\in(0,1]$, $D_h$ decoders with $d_{h,s}\ge\rho$ and $\varepsilon>0$; let $L$ and $\eta$ be as in (8) and $\hat\pi$ the finite planner of $\widetilde{\mathcal P}(L)$ started at $m_1$ (any admissible choice of its free choices).
--
--   1. The extension $\pi$ of $\hat\pi$ to $\widehat{\mathcal P}$ satisfies
--   $$V^*-V^{\pi}\le\frac\varepsilon4+2H^2\eta=\frac\varepsilon2,$$
--   where $V^*=V^*_{\mathcal P}$.
--   2. If $\varepsilon\le1$, every $\mathcal M_h$ is finite and
--   $$\sum_{h=1}^H|\mathcal M_h|\le\Big(\frac{C\,AOSH}{\varepsilon}\Big)^{3(L+1)}.\tag{9}$$
--
--   Clause 1 is the accuracy of the algorithm of Theorem 1 before derandomisation; clause 2 is the state count behind its running time.
--
--   Differences from the source:
--   - encoding: "the proposed planner π̂" run on P with private randomness, value V^π̂ → the extension of π̂ to P̂ (A.3), with value V^π_{P̂}; reason: running the planner on P while sampling X̂_h ∼ D_h(· | y_h) is, by the definition of P̂ (p.7), running its extension on P̂
--   - reading: L := min{H, ⌈(2/ρ) log(4H²/ε)⌉} (an integer ≥ 1 is required, p.8) → L := max{1, min{H, ⌈(2/ρ) log(4H²/ε)⌉}}; reason: for ε ≥ 4H² the printed ceiling is ≤ 0 and the killed POMDP is undefined; for ε < 4H² (and H ≥ 1) the value is the printed one
--   - generalization: "the proposed planner" → every admissible choice of the planner's free choices (`IsPlannerChoice`); reason: the paper leaves these choices free; the statement holds for each
--   - encoding: A, O, S, Σ_h |M_h| → cardinalities of the action, observation and state types; Σ over h ∈ [1 : H] of `Set.ncard`, with finiteness stated; reason: M_h is finite (it is a finite planner); stating finiteness rules out the junk value 0 of `ncard`
--   - generalization: standing assumptions of §3 (ρ ∈ (0, 1], an optimal decoder D_h with (D_h K_h)_{s,s} ≥ ρ) → any decoder family with d_{h,s} ≥ ρ (`IsRhoDecoderFamily P D ρ`), `0 < ρ ≤ 1` and `P.IsValid`; reason: the section's standing assumptions (pp.6–8) written as binders; the proofs never use optimality of D_h, so the paper's optimal decoders are a special case
--   - encoding: action space of size A (implicitly A ≥ 1) → `[Nonempty A]`; reason: with no action there is no policy; the paper's A ≥ 1
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), §4.3, p.12, (8)–(9)

import Mathlib
import Definitions.Def_DecodablePOMDP_Planner
import Definitions.Def_DecodablePOMDP_Params

namespace DecodablePOMDP

/-- **§4.3, p.12, (8)–(9) — error `ε/2` and planner size `(CAOSH/ε)^{3(L+1)}`.** There is a
universal constant `C > 0` such that for every valid POMDP `P` with a nonempty action set, every
`ρ ∈ (0, 1]`, every family of decoders with `d_{h,s} ≥ ρ` and every `ε > 0`, with
`L = min{H, ⌈(2/ρ) log(4H²/ε)⌉}` and `η = ε/(8H²)` of (8) and `π̂` the finite planner of `P̃(L)`
started at `m₁`:
1. the extension `π` of `π̂` to the augmented POMDP `P̂` (A.3) satisfies `V* − V^π ≤ ε/2`, where
   `V* = V*_P`;
2. if `ε ≤ 1`, every `M_h` is finite and `Σ_{h=1}^{H} |M_h| ≤ (C A O S H / ε)^{3(L+1)}`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §4.3, p.12: "Set L := min{H, ⌈(2/ρ) log
(4H²/ε)⌉} and η := ε/(8H²). (8) If L < H, then the choice of L gives H²(1 − ρ/2)^L ≤ H² exp(−ρL/2)
≤ ε/4. If L = H, there are only H − 1 reveal flags, so a run of L residual steps is impossible and
the killing loss is zero. Thus, in either case, the killing loss is at most ε/4. Combining this with
Theorem 2 and Theorem 3, the proposed planner π̂ has error at most V∗ − V^π̂ ≤ ε/4 + 2H²η = ε/2 < ε.
… Substituting the choice of η, the total number of finite planner states in the killed POMDP P̃, is
at most Σ_{h=1}^H |Mh| ≤ H(AOS)^{L+1}(C1H²/ε)^{L+1} ≤ (CAOSH/ε)^{3(L+1)}. (9) The last inequality
holds for 0 < ε ≤ 1 and a suitable universal constant C."

**Formalization Note.** The planner run on `P` with private randomness is, by the definition of
`P̂`, the extension `π` run on `P̂`, so `V^{π̂}` is `V^π_{P̂}`. The bound holds for every admissible choice of the planner's free choices.
`L = 1` when the printed ceiling is
`≤ 0` (`ε ≥ 4H²`), where the paper's `L` is undefined. `A, O, S` are the cardinalities of the
action, observation and state types. -/
theorem section_4_3_parameters :
    ∃ C : ℝ, 0 < C ∧
    ∀ (S A O : Type) [Fintype S] [Fintype A] [Fintype O] [DecidableEq S] [DecidableEq A]
      [Nonempty A] (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ ε : ℝ),
      P.IsValid → IsRhoDecoderFamily P D ρ → 0 < ρ → ρ ≤ 1 → 0 < ε →
      (∀ ch : PlannerChoice S A O (Lsel P.H ρ ε),
        IsPlannerChoice P D ρ (Lsel P.H ρ ε) (ηsel P.H ε) ch →
        optValue P - value (augmented P D) (extendPolicy (plannerPolicy P D ρ (Lsel P.H ρ ε)
          (ηsel P.H ε) ch (initState (Lsel P.H ρ ε)))) ≤ ε / 2) ∧
      (ε ≤ 1 →
        (∀ h, (plannerStates P D ρ (Lsel P.H ρ ε) (ηsel P.H ε) h).Finite) ∧
        ((∑ h ∈ Finset.Icc 1 P.H,
            (plannerStates P D ρ (Lsel P.H ρ ε) (ηsel P.H ε) h).ncard : ℕ) : ℝ) ≤
          (C * (Fintype.card A : ℝ) * (Fintype.card O : ℝ) * (Fintype.card S : ℝ) * (P.H : ℝ) /
            ε) ^ (3 * (Lsel P.H ρ ε + 1))) := by sorry

end DecodablePOMDP
