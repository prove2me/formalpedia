-- Prove2me | Theorems.Thm_BindingEntChannels_protocol_output_eq_filter
-- name    : BindingEntChannels.protocol_output_eq_filter
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:40:42.642512+00:00
-- url     : https://prove2.me/theorems/12e90e3a-8ac7-49b0-8671-3aa70efbc27f
-- title:
--   §II, p. 2 — every protocol's output comes from $N$ copies of $(I\otimes\Lambda)P^m_+$ by a local filter
-- statement:
--   Let $m\ge1$, let $\Lambda:M_m\to M_n$ be a channel, and consider any protocol (adaptive LQCC, post-selection allowed) that uses $\Lambda$ exactly $N$ times, starts from no shared state and outputs an unnormalized bipartite state $\omega$ on $\mathbb C^c\otimes\mathbb C^d$. Then there are $t>0$ and finitely many operators $A_i:(\mathbb C^m)^{\otimes N}\to\mathbb C^c$, $B_i:(\mathbb C^n)^{\otimes N}\to\mathbb C^d$ with
--
--   $$
--   \sum_i (A_i\otimes B_i)\,\big((I\otimes\Lambda)P^m_+\big)^{\otimes N}\,(A_i\otimes B_i)^\dagger\;=\;t\,\omega ,
--   $$
--
--   where Alice holds the $N$ reference halves and Bob the $N$ channel outputs.
--
--   So every state obtainable with $N$ channel uses is obtainable, without classical communication, from $N$ copies of $(I\otimes\Lambda)P^m_+$ by a local operation of the kind used in the definition of distillability. The paper states this for its "most general protocol": send half of a state $\sigma$ through $\Lambda^{\otimes N}$, then distill.
--
--   **Formalization Note** The left side is the platform's output of a local operation on $N$ copies (Eq. (4) of ref. [3]), with Alice's $N$ factors grouped first.
--
--   Differences from the source:
--   - generalization: the most general protocol sends half of some state σ through Λ^{⊗N} and then distills ϱ = (I ⊗ Λ^{⊗N})σ → every adaptive protocol with N channel uses (classical communication between uses, post-selection) has output proportional to a local operation applied to N copies of (I ⊗ Λ)P^m_+; reason: the paper's two-stage protocol is the special case without communication between channel uses, whose output has this form by M4, Eq. (2) and M7; the adaptive case is what Q2 allows
--   - encoding: P^m_+ of Eq. (1) for a dimension m → hypothesis 0 < m; reason: Eq. (1) divides by √m and is undefined at m = 0
--   - encoding: channel = completely positive trace-preserving map M_m → M_n → IsChannel: a finite Kraus family with Σ E†E = 1; reason: in finite dimension these are the same maps
--   - reading: LQCC operations → adaptive protocols that may also discard branches (post-selection); reason: the paper calls a non-trace-preserving Γ ⊗ I (p. 2) and filtering (p. 3) LQCC actions; this is the larger class, and the obtained state of M1 needs no post-selection, so nothing is lost for the deterministic class
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §II, p. 2 (proof of the Theorem: "The first stage of the most general protocol …")

import Mathlib
import Definitions.Def_BindingEntChannels_choiState
import Definitions.Def_BindingEntChannels_AdaptiveState
import Definitions.Def_BoundEntPPT_localOutput

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
§II, p. 2 (proof of the Theorem): "The first stage of the most general protocol of producing
singlet pairs is sending half of some state σ_{k×N,m×N} via the channel Λ^{⊗N} (denote it by
Λ^{n×N}_{m×N}). The second stage amounts to distillation of the emerging state
ϱ_{k×N,m×N} = (I_{k×N} ⊗ Λ^{n×N}_{m×N})σ."

Stated for every adaptive protocol: if `0 < m`, `Λ : M_m → M_n` is a channel and `run` is a
protocol (`AdaptiveState`) with output on `Fin c × Fin d` that uses `Λ` exactly `N` times and
starts from no shared state, then a positive multiple of its unnormalized output is produced by a
local operation, without communication, from `N` copies of `(I ⊗ Λ)P^m_+`:
`Σ_i (A_i ⊗ B_i) ((I ⊗ Λ)P^m_+)^{⊗N} (A_i ⊗ B_i)† = t · run(1)` for some `t > 0` and finite
families `A_i : (C^m)^{⊗N} → C^c`, `B_i : (C^n)^{⊗N} → C^d`.

**Formalization Note.** The left side is the published `BoundEntPPT.localOutput` (the operation
of Eq. (4) of ref. [3]), with Alice's `N` reference halves grouped first. The paper's two-stage
protocol (send half of `σ` through `Λ^{⊗N}`, then distill) is the special case without
classical communication between channel uses. -/
theorem protocol_output_eq_filter {m n c d N : ℕ} (hm : 0 < m)
    (Λ : QAlgorithms.Superop (Fin m) (Fin n)) (hΛ : QAlgorithms.IsChannel Λ)
    (run : QAlgorithms.Superop (Fin 1 × Fin 1) (Fin c × Fin d))
    (hrun : AdaptiveState Λ c d (n := N) run) :
    ∃ t : ℝ, 0 < t ∧ ∃ (r : ℕ) (A : Fin r → Matrix (Fin c) (Fin N → Fin m) ℂ)
      (B : Fin r → Matrix (Fin d) (Fin N → Fin n) ℂ),
        BoundEntPPT.localOutput (choiState Λ) N A B = (t : ℂ) • run 1 := by sorry

end BindingEntChannels
