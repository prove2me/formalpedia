-- Prove2me | Theorems.Thm_FlexRigidity_generic_dd_to_di_conversion
-- name    : FlexRigidity.generic_dd_to_di_conversion
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:29:08.051573+00:00
-- url     : https://prove2.me/theorems/b7abd003-e1ea-46c5-aae7-b636aa586f76
-- title:
--   Theorem 5.6 — generic DD-to-DI conversion: $\Pr_{\mathcal P'}[\mathrm{Acc}\wedge\mathrm{Bad}]\le q_{\mathrm{dep}}(\mu)^{\vartheta m}$
-- statement:
--   Let $\mathcal P_m$ be a device-dependent protocol with trusted preparation (Protocol 1) that satisfies Postulate Set 5.1 (security against $\mu$-depolarized trusted states with bound $q_{\mathrm{dep}}(\mu)^m$, $\limsup_{\mu\to0}q_{\mathrm{dep}}(\mu)<1$) and Postulate Set 5.3 (its ensemble is realized by measuring one entangled state $|\phi\rangle$, which is part of an optimal strategy of a nonlocal game $\mathsf G$ that self-tests it with measurement-only isometries). Let $\mathcal P'$ be its device-independent replacement (Protocol 2) with sequential shielded devices (Postulate Set 5.4). Then:
--
--   1. for every testing probability $\gamma\in(0,1)$
--   2. there is $\vartheta_0=\vartheta_0(\gamma)\in(0,1/2]$ such that
--   3. for every $0<\vartheta<\vartheta_0$
--   4. there are $\mu=\mu(\gamma,\vartheta)\in(0,1)$ and $\varepsilon_{\mathrm{tol}}=\varepsilon_{\mathrm{tol}}(\gamma,\vartheta)>0$, with $\varepsilon_{\mathrm{tol}}\to0$ as $\vartheta\to\vartheta_0$,
--
--   such that for every integer $n\ge4/(1-\gamma)$, every allowed implementation and attack, and every normalized initial state $\rho^0_{M_1R}$,
--   $$\Pr_{\mathcal P'}[\mathrm{Acc}_{\varepsilon_{\mathrm{tol}}}\wedge\mathrm{Bad}]\le q_{\mathrm{dep}}(\mu)^{\vartheta m},\qquad m=\lfloor(1-\gamma)n/2\rfloor.$$
--
--   Here $\mathrm{Acc}_{\varepsilon_{\mathrm{tol}}}$ is Alice's test $\|\mathrm{freq}_{\mathbf c}-P_C\|_{\mathrm{tr}}\le\varepsilon_{\mathrm{tol}}$ with $P_C=(1-\gamma,\gamma\omega^*,\gamma(1-\omega^*))$, and on acceptance the DD continuation runs on $(x_E,a_E)$ for the first $m$ generation rounds $E$ and on Bob's final memory. This is the paper's main result: any such trusted-preparation protocol can be run with untrusted devices at rate $m/n=(1-\gamma)/2$, with a soundness exponent that is a constant fraction $\vartheta$ of the device-dependent one.
--
--   **Formalization Note** The implementation consists of general instruments for Alice's device and for Bob in each round, with arbitrary memory dimensions; Bob's final register is his memory, the external information $R$ and his transcript $(u_i,y_i,b_i)$, identified with $\mathbb C^d$. $\Pr_{\mathcal P'}[\mathrm{Acc}\wedge\mathrm{Bad}]=\operatorname{Tr}[\mathrm{Bad}_\kappa\,\cdot\,\text{finalOp}]$, summing over accepted histories. The exponent $\vartheta m$ is a real power.
--
--   Differences from the source:
--   - generalization: a DD protocol P_m of the form of Protocol 1 with "every allowed attack" → every abstract experiment (Att m d, Bad_κ with 0 ≤ Bad_κ ≤ I) satisfying Postulate 5.1; reason: the proof uses P_m only through Postulate 5.1 (Lemma 5.13); every Protocol-1 protocol induces such an experiment
--   - generalization: pure states |ψ_{x,a}⟩ satisfying the realization condition (39) → the preparation ρ^{prep,µ} defined from (P_X, |ϕ⟩, {T^x_a}); reason: by (39) it equals (36); it also allows mixed conditional states
--   - reading: Postulate 5.1 "for every relevant 0 < µ < 1" and µ ∈ (0, 1) → Postulate 5.1 on (0, µbar) for a given µbar ∈ (0, 1], and µ(ϑ) ∈ (0, µbar); reason: the stronger reading: less is assumed
--   - reading: ϑ0, µ, εtol "depend on G and the function q_dep, but not n" (Theorem 1.2) → ϑ0, µ(·), εtol(·) are chosen after G, the realization, van_G, µbar and q_dep and before the experiment, n, the implementation, the attack and ρ⁰; reason: the stronger reading; the proof's choices (72)–(73) use only these data
--   - encoding: εtol(γ, ϑ) → 0 as ϑ → ϑ0(γ) → εtol is a function of ϑ with Tendsto εtol (𝓝[<] ϑ0) (𝓝 0); reason: γ is fixed; ϑ < ϑ0
--   - encoding: limsup_{µ→0} q_dep(µ) < 1 → ∃ q < 1, q_dep(µ) ≤ q eventually as µ → 0⁺; q_dep ≥ 0 on (0, µbar); reason: equivalent for real-valued q_dep; nonnegativity is implied by (37) and makes the real power q_dep(µ)^{ϑm} meaningful
--   - encoding: quantum registers, CPTP maps, instruments → registers Fin d, CP maps as finite Kraus families, channels as normalized Kraus families; reason: Choi–Kraus in finite dimension
--   - reading: R is "external side information" of ρ⁰_{M_1R} → R is part of Bob's final register, with M^B_{n+1} and his transcript (u_i, y_i, b_i); reason: the stronger reading: the attack may use R
--   - encoding: εtol > 0 → εtol(ϑ) ∈ (0, (1−γ)/2]; reason: (1−γ)/2 is Protocol 2's parameter condition, needed for E to exist on acceptance
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Theorem 5.6, eq. (45), p. 43 (informal form Theorem 1.2, pp. 5–6); Protocols 1–2, pp. 37, 41; Postulate Sets 5.1, 5.3, 5.4, pp. 38–40

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Postulate53iii
import Definitions.Def_FlexRigidity_Postulate51
import Definitions.Def_FlexRigidity_prepState
import Definitions.Def_FlexRigidity_realRound
import Definitions.Def_FlexRigidity_seqRun
import Definitions.Def_FlexRigidity_finalOp
import Definitions.Def_FlexRigidity_PC
import Definitions.Def_HybridXorLift_tvDist
import Definitions.Def_FlexRigidity_freq
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

open Classical in
/-- **Theorem 5.6 (Generic DD-to-DI conversion)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 43; informal form Theorem 1.2, pp. 5–6). Let `P_m`
be a DD protocol of the form given in Protocol 1, satisfying Postulate Sets 5.1 and 5.3. Let `P′` be
its DI replacement from Protocol 2 in a sequential setting where Postulate Set 5.4 holds. Then,
for every testing probability `γ ∈ (0, 1)` there exists `ϑ0 = ϑ0(γ) ∈ (0, 1/2]` such that, for every
`0 < ϑ < ϑ0(γ)`, there exist `µ = µ(γ, ϑ) ∈ (0, 1)` and `εtol = εtol(γ, ϑ) > 0` with
`εtol(γ, ϑ) → 0` as `ϑ → ϑ0(γ)` for fixed `γ`, such that, for every integer `n ≥ 4/(1−γ)`, every
allowed implementation and attack, and every normalized initial state `ρ⁰_{M_1R}`,
`Pr_{P′}[Acc_εtol ∧ Bad] ≤ (q_dep(µ))^{ϑm}` (45), `m = ⌊(1−γ)n/2⌋`.

**Formalization Note** The data fixed first are the game `G`, its realization (Postulate 5.3(i)–(ii)),
`van_G` (5.3(iii)), `µbar ∈ (0, 1]` and `q_dep ≥ 0` on `(0, µbar)` with `limsup_{µ→0} q_dep(µ) < 1` (as: there is
`q < 1` with `q_dep ≤ q` eventually as `µ → 0⁺`). `ϑ0`, `µ(·)`, `εtol(·)` are chosen next and do not
depend on the DD experiment, `n`, the implementation, the attack or `ρ⁰` (Theorem 1.2: they "depend
on G and the function q_dep, but not n"). The DD protocol is any abstract experiment `(Att, Bad)`
satisfying Postulate 5.1 on `(0, µbar)` with the preparations (36) defined from the realization.
The devices are general instruments (Postulate 5.4); Bob's final register is his memory, the
external information `R` and his transcript `(u_i, y_i, b_i)`. `εtol ≤ (1−γ)/2` is Protocol 2's
parameter condition. The exponent `ϑm` is real (`rpow`). -/
theorem generic_dd_to_di_conversion {X Y A B SA SB : Type} [Fintype X] [Fintype Y] [Fintype A]
    [Fintype B] [Fintype SA] [Fintype SB] [DecidableEq X] [DecidableEq Y] [DecidableEq A]
    [DecidableEq B] [DecidableEq SA] [DecidableEq SB]
    (G : Game X Y A B) (Rz : Realization X Y A B SA SB) (van : ℝ → ℝ) (μbar : ℝ)
    (qdep : ℝ → ℝ) (hG : G.IsValid) (hRz : Rz.IsPostulate53ii G) (hST : Postulate53iii G Rz van)
    (hμbar : 0 < μbar ∧ μbar ≤ 1) (hq0 : ∀ μ ∈ Set.Ioo 0 μbar, 0 ≤ qdep μ)
    (hq : ∃ q < 1, ∀ᶠ μ in 𝓝[>] (0 : ℝ), qdep μ ≤ q) :
    ∀ γ ∈ Set.Ioo (0 : ℝ) 1, ∃ ϑ0 ∈ Set.Ioc (0 : ℝ) (1 / 2), ∃ μf εf : ℝ → ℝ,
      Tendsto εf (𝓝[<] ϑ0) (𝓝 0) ∧
      ∀ ϑ ∈ Set.Ioo 0 ϑ0, μf ϑ ∈ Set.Ioo 0 μbar ∧ εf ϑ ∈ Set.Ioc 0 ((1 - γ) / 2) ∧
        ∀ DD : DDExperiment X A, DD.IsValid → Postulate51 DD (prepState Rz) qdep μbar →
        ∀ n : ℕ, 4 / (1 - γ) ≤ (n : ℝ) →
        ∀ I : DIImpl X Y A B, I.IsAllowed n →
        ∀ (r : ℕ) (ρ0 : Matrix (Fin r × (Fin (I.dA 0) × Fin (I.dB 0)))
            (Fin r × (Fin (I.dA 0) × Fin (I.dB 0))) ℂ), Density ρ0 →
        ∀ κ : DD.Att ⌊(1 - γ) * n / 2⌋₊
            (Fintype.card ((Fin n → Bool × Option Y × Option B) × (Fin r × Fin (I.dB n)))),
          tr (DD.Bad _ _ κ * finalOp ⌊(1 - γ) * n / 2⌋₊
              (fun h => HybridXorLift.tvDist (freq (Hist.cs n h)) (PC γ (quantumValue G)) ≤ εf ϑ)
              (seqRun (M := fun k => Fin (I.dA k) × Fin (I.dB k)) (realRound G Rz γ I) ρ0 n)) ≤
            qdep (μf ϑ) ^ (ϑ * (⌊(1 - γ) * n / 2⌋₊ : ℝ)) := by sorry

end FlexRigidity
