-- Prove2me | Theorems.Thm_AgnosticTNS_claim_2_2
-- name    : AgnosticTNS.claim_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:35:35.010213+00:00
-- url     : https://prove2.me/theorems/c71a584e-b701-49fc-8125-d6fc75a48bca
-- title:
--   Claim 2.2 — rank bound across a TN cut
-- statement:
--   Let $G=([n],E)$ be a graph, $w:E\to\mathbb N$, and $|\psi\rangle\in S_d(G,w)$. For every subset $S\subseteq[n]$,
--   $$
--   \operatorname{rank}\big(\mathrm{tr}_{[n]\setminus S}[|\psi\rangle\langle\psi|]\big)\le\prod_{e\in\mathrm{cut}_G(S)}w(e),
--   $$
--   with the empty product equal to $1$. In particular, if $w(e)\le\chi$ for every edge, then
--   $$
--   \operatorname{rank}\big(\mathrm{tr}_{[n]\setminus S}[|\psi\rangle\langle\psi|]\big)\le\chi^{|\mathrm{cut}_G(S)|}.
--   $$
--   The reduced-state rank equals the Schmidt rank across $S\mid[n]\setminus S$, so tensor network states have small Schmidt rank across every vertex set with a small cut.
--
--   Differences from the source:
--   - encoding: vertices $[n]$, labels $[d]$, steps $[L]$ (1-based), vectors in $(\mathbb C^d)^{\otimes n}$ → `Fin n`, `Fin d`, `Fin L` (0-based), functions `(Fin n → Fin d) → ℂ`; reason: Lean convention; same instances
--   - encoding: standing assumptions $n\ge1$, $d\ge2$, $\epsilon\in(0,1]$, $\delta\in(0,1)$ of p.11 → explicit hypotheses; reason: the section's standing assumptions are binders
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Claim 2.2, Eqs. (2.4)–(2.5), p.12

import Mathlib
import Definitions.Def_AgnosticTNS_TNS
import Definitions.Def_AgnosticTNS_cut
import Definitions.Def_AgnosticTNS_ptrace
open Matrix
open scoped ComplexOrder

namespace AgnosticTNS

/-- **Claim 2.2 (Rank bound across a TN cut)**, p.12 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Let `G = ([n], E)` be a graph,
`w : E → ℕ` and `|ψ⟩ ∈ S_d(G, w)`. For every `S ⊆ [n]`,
`rank(tr_{[n]∖S}[|ψ⟩⟨ψ|]) ≤ Π_{e ∈ cut_G(S)} w(e)` (2.4), and if `w(e) ≤ χ` for every edge then
`rank(tr_{[n]∖S}[|ψ⟩⟨ψ|]) ≤ χ^{|cut_G(S)|}` (2.5).

**Formalization Note** `|ψ⟩⟨ψ|` is `vecMulVec ψ (star ψ)`; standing assumptions `n ≥ 1`, `d ≥ 2` (p.11). -/
theorem claim_2_2 {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) (G : SimpleGraph (Fin n))
    (w : G.edgeSet → ℕ) (ψ : (Fin n → Fin d) → ℂ) (hψ : ψ ∈ TNS d G w) (S : Finset (Fin n)) :
    (ptrace S (vecMulVec ψ (star ψ))).rank ≤ ∏ e ∈ cut G S, w e ∧
      ∀ χ : ℕ, (∀ e, w e ≤ χ) → (ptrace S (vecMulVec ψ (star ψ))).rank ≤ χ ^ (cut G S).card := by sorry

end AgnosticTNS
