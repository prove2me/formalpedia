-- Prove2me | Theorems.Thm_CompDesign_theorem_4_1
-- name    : CompDesign.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:59:51.97329+00:00
-- url     : https://prove2.me/theorems/526bfa4e-c30e-42ab-8253-8443370e1e37
-- title:
--   Theorem 4.1 — strict better responses in $\Gamma^{mc}$ terminate, so a pure Nash equilibrium exists
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget, $c_i\ge 0$ the private costs, and $v:2^N\to\mathbb R$ a value function satisfying Assumption 3.1: $v(\emptyset)=0$, $v$ monotone ($S\subseteq S'\Rightarrow v(S)\le v(S')$) and submodular ($v(S\cup\{i\})-v(S)\ge v(S'\cup\{i\})-v(S')$ whenever $S\subseteq S'$ and $i\notin S'$). The marginal-contribution payment is $p^{mc}_i(S)=B\,\frac{v(S)-v(S\setminus\{i\})}{v(S)}$ if $i\in S$ and $v(S)>0$, and $0$ otherwise (8); agent $i$'s utility is $u_i(S)=p^{mc}_i(S)-c_i$ if $i\in S$ and $0$ otherwise.
--
--   **Theorem 4.1 (Existence of pure Nash equilibria).** Let $\max_{i\in N}c_i<B$. In the game $\Gamma^{mc}$ induced by the marginal contribution payment rule (8):
--
--   1. every sequence of strict better responses terminates: there is no infinite sequence $S_0,S_1,S_2,\dots$ in which each $S_{t+1}$ is a strict better response from $S_t$;
--   2. as a result, $\Gamma^{mc}$ admits a pure Nash equilibrium.
--
--   This is the existence half of Main Result 2. It shows that simple best-response dynamics, run by the agents themselves, always settle.
--
--   **Formalization Note** A strict better response is `CompDesign.IsStrictImprovement`: one agent switches its participation and its own utility strictly rises.
--
--   Differences from the source:
--   - encoding: every sequence of strict better responses terminates → there is no f : ℕ → Finset (Fin n) with a strict better response from f t to f (t+1) for every t; reason: a sequence terminates iff it is not infinite; this is the standard well-foundedness formulation
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), §4.1, Theorem 4.1, p.17 (PDF 20)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesign_IsStrictImprovement

open CompDesignBFM

namespace CompDesign

/-- Theorem 4.1 (Existence of pure Nash equilibria), §4.1, p.17 (PDF 20) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…).
Let `max_{i∈N} c_i < B`. In the game `Γ^mc` induced by the marginal contribution payment rule (8),
every sequence of strict better responses terminates. As a result, `Γ^mc` admits a pure Nash
equilibrium.

**Formalization Note.** Assumption 3.1 (`v ∅ = 0`, monotone, submodular), `B > 0` and `c ≥ 0` are the
standing assumptions of §3.1. "Every sequence of strict better responses terminates" is stated as: there
is no infinite sequence `S₀, S₁, …` in which each `S_{t+1}` is a strict better response from `S_t`. -/
theorem theorem_4_1 {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ i, 0 ≤ c i)
    (hcB : ∀ i, c i < B) :
    (¬ ∃ f : ℕ → Finset (Fin n), ∀ t, IsStrictImprovement v B c (f t) (f (t + 1))) ∧
    ∃ S : Finset (Fin n), IsPNE v B c S := by sorry

end CompDesign
