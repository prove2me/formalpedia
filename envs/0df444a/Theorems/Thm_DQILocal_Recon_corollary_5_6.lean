-- Prove2me | Theorems.Thm_DQILocal_Recon_corollary_5_6
-- name    : DQILocal.Recon.corollary_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:56.865729+00:00
-- url     : https://prove2.me/theorems/9b6a95a4-ae0f-4d95-b17c-3febdafbb1f7
-- title:
--   Corollary 5.6 — local estimates in random instances: the optimal $t$-local estimate at a typical symbol succeeds w.p. exactly $P_t$; $P_{\lfloor c_0\log m\rfloor}\to1$ iff non-reconstruction
-- statement:
--   Let $q\ge2$, $f$ any cost, $\beta\ge0$, $k\ge2$, $D\ge3$, $k<D$, and $0<c_0<1/(2\ln((k-1)(D-1)))$. Write $p=p_\beta$.
--
--   **(A) The local conditions are typical.** For every sequence of depths $t_m\le c_0\ln m$, with probability tending to one over random $(k,D)$-regular instances over $\mathbb Z_q$ from the configuration model or from Gallager's ensemble, $\mathrm{LT}_{t_m}(i)$ and $\mathrm{TP}_{t_m}(i)$ hold; this holds for a uniformly random symbol $i$ and also for any fixed symbol $i=i_m$.
--
--   **(B) On this event.** For every $(k,D)$-regular instance $B$, every symbol $i$ and every $t$ at which $\mathrm{LT}_t(i)$ and $\mathrm{TP}_t(i)$ hold:
--
--   1. the conclusion of Theorem 5.2 holds at $i$: every decoder making a $t$-local estimate at $i$ has symbol error at least $1-P_t\ge1-P_\infty$ and block success at most $P_t$; $1-P_\infty>0$ under reconstruction; and for $q=2$, $f(z)=z$, $1-P_t\ge\frac14\sigma_\beta^2\bar{\mathfrak m}_\infty^{2k}$;
--   2. the bound is attained: some decoder making a $t$-local estimate at $i$ has $\Pr[\hat c_i=c_i]=P_t$ exactly;
--   3. the largest probability with which a $t$-local estimate at $i$ equals $c_i$ is $P_t$;
--   4. the ball of radius $2t$ around $i$ is isomorphic to $\mathcal T_t$, and depth-$t$ BPQM for symbol $i$ — transported along any such isomorphism, with any choice of symbol-node unitaries — is a measurement on the qudits of $N_t(i)$ whose estimate equals $c_i$ with probability $P_t$.
--
--   **(C) The threshold.**
--   $$P_{\lfloor c_0\ln m\rfloor}\longrightarrow1\ (m\to\infty)\iff\text{the primal model has non-reconstruction.}$$
--
--   This is the formal version of the paper's first main theorem: local quantum decoders for DQI on random sparse instances succeed exactly up to the tree-reconstruction threshold of the primal Gibbs measure, and BPQM is an optimal local decoder.
--
--   Differences from the source:
--   - reading: for t ≤ c₀ log m … with probability 1 − o(1) → for every sequence t_m ≤ c₀ ln m the probability tends to 1, along the m with D ∣ km (configuration model), resp. D ∣ m (Gallager); reason: uniformity in t is the stronger reading; the ensembles are defined only at those m
--   - encoding: the same holds for any fixed symbol i → for every sequence of symbols i_m ∈ [m + 1], Pr_B[LT ∧ TP at i_m] → 1 at size m + 1 for both ensembles; reason: a fixed symbol must exist at every size; indexing sizes from 1 avoids the empty [0]
--   - generalization: on the event (random instances where LT_t(i) and TP_t(i) hold), the conclusion of Theorem 5.2 and its attainment → for every (k, D)-regular B, symbol i and depth t with LT_t(i) and TP_t(i); reason: the event consists of such instances, so the Lean statement specializes to the paper's
--   - reading: depth-t BPQM for symbol i computes such an estimate → the ball is isomorphic to T_t (Nonempty TreeIso), and BPQM transported along every isomorphism, for every BPQMChoice, is a POVM on N_t(i) with success P_t; reason: the paper fixes neither the symbol-node unitaries nor the order of the children; all choices is the stronger reading; p. 30 gives the isomorphism ("C_t(i) is the tree code C_t")
--   - reading: the largest probability with which a t-local estimate at i equals c_i → sSup of 1 − symbolError over all decoders (POVMs) that make a t-local estimate at i; reason: literal reading of the sentence
--   - encoding: a measurement (possibly with ancillas and work registers) → a POVM on the system (positive semidefinite elements summing to the identity); reason: Naimark dilation: the two describe the same outcome laws
--   - encoding: the configuration model (half-edge pairing conditioned on no multiple edges) → the uniform law on (k, D)-regular m × (km/D) 0/1 matrices; reason: each simple biregular labelled graph arises from exactly (k!)^m (D!)^n bijections; p. 3 states the same law
--   - encoding: P_∞ = lim P_t, m̄_∞ = lim m̄_t → ⨆ t, P_t and ⨅ t, m̄_t; reason: monotone bounded sequences; same values
--   - encoding: t = ⌊c₀ log m⌋, natural logarithm → Nat.floor (c₀ * Real.log m); reason: t is a natural number; Real.log is ln
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Corollary 5.6, p. 35 (informal: Main Theorem 1, p. 6)

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_SpectralRecursion
import Definitions.Def_DQILocal_Recon_LocalConditions
import Definitions.Def_DQILocal_Recon_Decoder
import Definitions.Def_DQILocal_Recon_TreeCode
import Definitions.Def_DQILocal_Recon_BPQM
import Definitions.Def_DQILocal_Recon_Reconstruction
import Definitions.Def_DQILocal_Recon_Ensembles

namespace DQILocal.Recon

open scoped BigOperators ComplexOrder
open Filter Topology

/-- **Corollary 5.6 (Local estimates in random instances).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Corollary 5.6, p. 35
(informal version: Main Theorem 1, p. 6).
"Let `q ≥ 2`, let `f` be any cost, let `k ≥ 2`, `D ≥ 3`, and `k < D`, and let
`0 < c₀ < 1/(2 log((k − 1)(D − 1)))`, with the natural logarithm. For `t ≤ c₀ log m` and a uniformly
random symbol `i`, with probability `1 − o(1)` over random `(k, D)`-regular instances over `ℤ_q`
from the configuration model or from Gallager's ensemble, `LT_t(i)` and `TP_t(i)` hold, so the
conclusion of Theorem 5.2 holds at `i`. On this event, the bound of Theorem 5.2 on the symbol error
is attained: some `t`-local estimate at `i` equals `c_i` with probability exactly `P_t`, and
depth-`t` BPQM for symbol `i` computes such an estimate. In particular, for `t = ⌊c₀ log m⌋`, the
largest probability with which a `t`-local estimate at `i` equals `c_i` is `P_t`, and `P_t` tends to
one as `m → ∞` if and only if the primal model has non-reconstruction. The same holds for any fixed
symbol `i`."

The statement has three parts.
(A) For every sequence `t_m ≤ c₀ ln m`, `Pr[LT_{t_m}(i) ∧ TP_{t_m}(i)] → 1` for both ensembles, for
a uniformly random symbol and for every sequence of fixed symbols.
(B) For every `(k, D)`-regular instance and every symbol `i` and depth `t` with `LT_t(i)` and
`TP_t(i)`: the whole conclusion of Theorem 5.2; a decoder making a `t`-local estimate at `i` with
success exactly `P_t`; the optimum over such decoders equals `P_t`; the ball is isomorphic to `T_t`,
and depth-`t` BPQM transported along **every** isomorphism, with **every** choice of symbol-node
unitaries, is a POVM on the qudits of `N_t(i)` whose estimate equals `c_i` with probability `P_t`.
(C) `P_{⌊c₀ ln m⌋} → 1` as `m → ∞` iff the primal model has non-reconstruction.

**Formalization Note.** (A) is read uniformly in `t` (every sequence `t_m`), along the `m` at which
each ensemble is defined (`D ∣ km`, resp. `D ∣ m`); the fixed-symbol clause takes a symbol
`i_m ∈ [m+1]` for each size `m + 1`. (B) is stated for every regular instance, not only for the
random ones on the event; it specializes to the paper's claim. `P_t`, the optimum `optLocal`, and the
BPQM success are defined independently. Decoders and local estimates are POVMs (ancillas absorbed
by Naimark). The binary clause is for `q = 2`, `f(z) = z.val`, `σ_β = tanh(β/2)`. -/
theorem corollary_5_6 (q : ℕ) [NeZero q] (hq : 2 ≤ q) (f : ZMod q → ℝ) (k D : ℕ) (hk : 2 ≤ k)
    (hD : 3 ≤ D) (hkD : k < D) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hc₀' : c₀ < 1 / (2 * Real.log (((k : ℝ) - 1) * ((D : ℝ) - 1)))) (β : ℝ) (hβ : 0 ≤ β) :
    -- (A) the local conditions are typical
    (∀ t : ℕ → ℕ, (∀ m : ℕ, (t m : ℝ) ≤ c₀ * Real.log m) →
      Tendsto (fun m => configProb k D q (t m) m) (atTop ⊓ 𝓟 {m | D ∣ k * m}) (𝓝 1) ∧
      Tendsto (fun m => gallagerProb k D q (t m) m) (atTop ⊓ 𝓟 {m | D ∣ m}) (𝓝 1) ∧
      ∀ i : (m : ℕ) → Fin (m + 1),
        Tendsto (fun m => configProbAt k D q (t (m + 1)) (m + 1) (i m))
          (atTop ⊓ 𝓟 {m | D ∣ k * (m + 1)}) (𝓝 1) ∧
        Tendsto (fun m => gallagerProbAt k D q (t (m + 1)) (m + 1) (i m))
          (atTop ⊓ 𝓟 {m | D ∣ m + 1}) (𝓝 1)) ∧
    -- (B) on the event: Theorem 5.2's conclusion, and its attainment
    (∀ {m : ℕ} {κ : Type} [Fintype κ] (B : Matrix (Fin m) κ Bool), IsRegular k D B →
      ∀ (i : Fin m) (t : ℕ), LT B i t → TP q B i t →
        (∀ F : (Fin m → ZMod q) → Matrix (Fin m → ZMod q) (Fin m → ZMod q) ℂ, IsPOVM F →
          IsLocalEstimate q (gibbsWeight q f β) B i t F →
            1 - Pt k D q f β t ≤ symbolError (gibbsWeight q f β) B F i ∧
              blockSuccess (gibbsWeight q f β) B F ≤ Pt k D q f β t) ∧
        1 - Pinf k D q f β ≤ 1 - Pt k D q f β t ∧
        (HasRecon k D q f β → 0 < 1 - Pinf k D q f β) ∧
        (q = 2 → (∀ z : ZMod q, f z = (z.val : ℝ)) →
          (1 / 4) * Real.tanh (β / 2) ^ 2 * mbarInf k D q f β ^ (2 * k) ≤ 1 - Pt k D q f β t) ∧
        (∃ F : (Fin m → ZMod q) → Matrix (Fin m → ZMod q) (Fin m → ZMod q) ℂ, IsPOVM F ∧
          IsLocalEstimate q (gibbsWeight q f β) B i t F ∧
            1 - symbolError (gibbsWeight q f β) B F i = Pt k D q f β t) ∧
        optLocal q (gibbsWeight q f β) B i t = Pt k D q f β t ∧
        Nonempty (TreeIso k D B i t) ∧
        ∀ (φ : TreeIso k D B i t) (U : BPQMChoice q),
          IsPOVM (φ.transport (bpqm k D t (gibbsWeight q f β) U)) ∧
            localSuccess (gibbsWeight q f β) B i t (φ.transport (bpqm k D t (gibbsWeight q f β) U)) =
              Pt k D q f β t) ∧
    -- (C) the threshold
    (Tendsto (fun m : ℕ => Pt k D q f β ⌊c₀ * Real.log m⌋₊) atTop (𝓝 1) ↔
      NonRecon k D q f β) := by sorry

end DQILocal.Recon
