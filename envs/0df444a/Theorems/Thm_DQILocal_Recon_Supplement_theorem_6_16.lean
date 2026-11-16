-- Prove2me | Theorems.Thm_DQILocal_Recon_Supplement_theorem_6_16
-- name    : DQILocal.Recon.Supplement.theorem_6_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:31:25.417199+00:00
-- url     : https://prove2.me/theorems/652d0fb4-599f-4463-9b03-a0c4365e6984
-- title:
--   Theorem 6.16, p. 52 — union bound for random regular codes: $U_C(\theta)\to0$ in probability
-- statement:
--   Let $k\ge3$, $D\ge2$, $\theta\in(0,1]$, $A=e^{1+2^{D-1}k/D}$ and $\varepsilon=(2A)^{-1/(k/2-1)}$. Suppose there is $\eta>0$ such that for every $u\in[\varepsilon,1]$ some $x>0$ satisfies
--   $$G_{k,D}(u,x;\theta)\le-\eta u .$$
--   Then for random $(k,D)$-regular instances from the configuration model, with or without the conditioning on the absence of multiple edges, the weight enumerator $U_C(\theta)=\sum_{c\in C\setminus\{0\}}\theta^{|c|}$ of the binary code $C$ tends to $0$ in probability: for every $\delta>0$, $\Pr_B[U_C(\theta)>\delta]\to0$ as $m\to\infty$ with $D\mid km$.
--
--   Through Proposition 6.15, this makes Prange's algorithm an approximate Gibbs sampler on random instances, which gives the unconditional quadratic bound of Corollary 6.17.
--
--   Differences from the source:
--   - reading: "the configuration model" (the proof works without the conditioning and transfers to the conditioned ensemble, p. 52) → both laws: the pairing model reduced modulo two and the uniform law on regular matrices; reason: both readings of the model are covered; neither is weaker
--   - encoding: U_C(θ) → 0 in probability → for every δ > 0, Pr_B[δ < U_C(θ)] → 0 along admissible m (D ∣ km); reason: the definition of convergence in probability; the model exists only for admissible m
--   - encoding: q = 2 (standing assumption of §6.3.3) → the code of B over ZMod 2; reason: the standing assumption
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 6.16, p. 52; definitions pp. 50–51

import Mathlib
import Definitions.Def_DQILocal_Recon_LocalConditions
import Definitions.Def_DQILocal_Recon_Decoder
import Definitions.Def_DQILocal_Recon_Supplement_Thresholds
import Definitions.Def_DQILocal_Recon_Supplement_ConfigModel
import Definitions.Def_DQILocal_Recon_Supplement_UnionBound

namespace DQILocal.Recon.Supplement

open scoped BigOperators
open DQILocal.Recon Filter Topology

/-- **Theorem 6.16 (Union bound for random regular codes).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 6.16, p. 52.
"Let `k ≥ 3`, `D ≥ 2`, `θ ∈ (0, 1]`, `A = e^{1+2^{D-1}k/D}` and `ε = (2A)^{-1/(k/2-1)}`. Suppose
there is `η > 0` such that for every `u ∈ [ε, 1]` some `x > 0` satisfies `G_{k,D}(u, x; θ) ≤ -ηu`.
Then for the configuration model of random `(k, D)`-regular instances, `U_C(θ) → 0` in
probability."

**Formalization Note.** `q = 2` throughout §6.3.3 (p. 50); `C` is the binary code of `B`. The
conclusion is stated for both laws of `B`: the configuration model without the conditioning
(`pairing`, in which the proof works) and with the conditioning on no multiple edges (`simple`, the
model of §5.1; "The transfer to the ensemble without multiple edges is as in Section 5.1", p. 52).
"`→ 0` in probability" is: for every `δ > 0`, `Pr_B[U_C(θ) > δ] → 0` as `m → ∞` along the
admissible `m` (`D ∣ km`, `n = km/D`). -/
theorem theorem_6_16 (k D : ℕ) (hk : 3 ≤ k) (hD : 2 ≤ D) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hG : ∃ η : ℝ, 0 < η ∧ ∀ u ∈ Set.Icc (epsUB k D) 1, ∃ x : ℝ, 0 < x ∧ Gfun k D u x θ ≤ -η * u) :
    ∀ L : CfgLaw, ∀ δ : ℝ, 0 < δ →
      Tendsto (fun m => cfgProb L k D m (fun B => δ < weightEnum B θ))
        (admissible k D) (𝓝 0) := by sorry

end DQILocal.Recon.Supplement
