-- Prove2me | Theorems.Thm_DQILocal_Recon_theorem_4_6
-- name    : DQILocal.Recon.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:19.164421+00:00
-- url     : https://prove2.me/theorems/f9d0dd33-6e6a-48ec-a88b-400422fe2fc2
-- title:
--   Theorem 4.6 — decoder–reconstruction duality: $[C^{(t)}]\overset{d}{=}[RM^{(t+1)}]$, and $P_t\to1$ iff non-reconstruction
-- statement:
--   For every $q\ge2$, every cost $f$, every $\beta\ge0$ (and $k,D\ge2$):
--
--   1. for every $t\ge0$, the translation orbits $[\nu]=\{\nu(\cdot+g):g\in\mathbb Z_q\}$ of the spectrum $C^{(t)}$ of the spectral recursion and of the reflected root posterior $RM^{(t+1)}$ of the planted model on $\mathcal T'_{t+1}$ have the same law:
--   $$[C^{(t)}]\overset{d}{=}[RM^{(t+1)}] ;$$
--   2. $P_t\to1$ as $t\to\infty$ if and only if the primal model has non-reconstruction.
--
--   The quantum check node and the primal variable node perform the same random operation on translation orbits, so the decoding problem on the $(k,D)$ tree is dual to tree reconstruction for the primal Gibbs measure with node types exchanged.
--
--   Differences from the source:
--   - reading: [C^(t)] =^m [R M^(t+1)] (an "m" printed over the equality sign) → equality in distribution of the translation orbits: every union of translation orbits A has the same probability under the law of C^(t) and under the law of R M^(t+1); reason: the proof writes =^d for the same identities (p. 26); the printed m is a typo
--   - encoding: random spectra and the planted model → finite weighted lists (FinLaw) and finite sums over the planted space; M^(t+1) as the explicit posterior ratio; reason: all laws involved are finitely supported; same laws
--   - encoding: M^(t) → u in probability → for every ε > 0, Pr[‖M^(t) − u‖ > ε] → 0 with the sup norm; reason: all norms on ℝ^{ℤ_q} are equivalent
--   - encoding: the primal tree T'_{t+1} and its vertices → index paths (List ℕ): root variable [], child clauses v ++ [a] (a < D − 1), child variables j ++ [b] (b < k − 1); ∂j = the parent and child variables of clause j; reason: a labelling of the same tree
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 4.6, p. 26

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_SpectralRecursion
import Definitions.Def_DQILocal_Recon_Reconstruction

namespace DQILocal.Recon

open scoped BigOperators
open Filter Topology

/-- **Theorem 4.6 (Decoder–reconstruction duality).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 4.6, p. 26.
"For every `q ≥ 2`, every cost `f`, every `β ≥ 0`, and every `t ≥ 0`:
1. The translation orbits satisfy `[C^{(t)}] =^m [R M^{(t+1)}]`.
2. `P_t → 1` if and only if the primal model has non-reconstruction."

Here `[ν] = {ν(· + g) : g ∈ ℤ_q}` (p. 26), `C^{(t)}` is the spectral recursion (Definition 4.2)
and `M^{(t+1)}` the root posterior of the planted model on `T'_{t+1}` (§4.3).

**Formalization Note.** Part 1 is read as equality in distribution of the translation orbits (the
symbol printed over `=` is read as the proof's `=^d`, p. 26): every set `A` of vectors that is a
union of translation orbits has the same probability under the law of `C^{(t)}` and under the law
of `R M^{(t+1)}`. Standing assumptions `k ≥ 2`, `D ≥ 2` (§3.1, p. 15). -/
theorem theorem_4_6 (q : ℕ) [NeZero q] (hq : 2 ≤ q) (f : ZMod q → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (k D : ℕ) (hk : 2 ≤ k) (hD : 2 ≤ D) :
    (∀ t : ℕ, ∀ A : Set (ZMod q → ℝ),
      (∀ (ν : ZMod q → ℝ) (g : ZMod q), ν ∈ A ↔ (fun z => ν (z + g)) ∈ A) →
        (specC k D (gibbsWeight q f β) t).prob A =
          plantedProb k D (t + 1) (gibbsWeight q f β)
            (fun ω => refl (rootPosterior k D (t + 1) (gibbsWeight q f β) ω) ∈ A)) ∧
    (Tendsto (fun t => Pt k D q f β t) atTop (𝓝 1) ↔ NonRecon k D q f β) := by sorry

end DQILocal.Recon
