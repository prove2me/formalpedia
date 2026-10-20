-- Prove2me | Theorems.Thm_AtomicDynRouting_ResidenceTime_claim_1
-- name    : AtomicDynRouting.ResidenceTime.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:15.224794+00:00
-- url     : https://prove2.me/theorems/acfba523-0003-4e39-b6be-772ba8b514fa
-- title:
--   Claim 1, p. 9 — if token k departs from v ∈ Vk, it does so no later than r0 + (Loζdζ − Lvdζ + k − 1)
-- statement:
--   Let $G$ be a finite acyclic network with unit lengths and capacities, take an ADR run, a focal agent $\zeta$ with entry time $r$, an integer time $r_0\ge r$, and the token process of §3.2 started at $r_0$. Write $L=L_{o_\zeta d_\zeta}$.
--
--   Let $k\ge2$, and assume the conclusion of Lemma 1 for the tokens $1,\dots,k-1$. Let $e$ be an edge of $G_\zeta$ with tail $v$, and suppose that
--
--   1. token $k$ departs from $v$ along $e$ at time $s$: it is in the buffer of $e$ at time $s$ and not at time $s+1$;
--   2. it does so right after a smaller token: some token $h$ with $1\le h<k$ departed from $v$ along $e$ at time $s-1$ (it was in the buffer of $e$ at time $s-1$ and not at time $s$).
--
--   Then
--   $$s\ \le\ r_0+\bigl(L-L_{v d_\zeta}+k-1\bigr).$$
--
--   The vertices $v$ of this kind form the set $V_k$ of the paper. This is the first case of the induction step in the proof of Lemma 1.
--
--   **Formalization Note.** The bound is stated additively, $s+L_{vd_\zeta}+1\le r_0+L+k$. "Right after" is read as one time unit later through the same edge, which is how the paper's proof uses it (token $k$ departs one unit after token $h$, whose bound is $r_0+(L-L_{vd_\zeta}+h-1)$). The induction hypothesis is a hypothesis of the statement, as on the page.
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), p. 9 (PDF 10), §3.2, proof of Lemma 1, definition of Vk and Claim 1

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Tokens

namespace AtomicDynRouting.ResidenceTime

/-- Claim 1, §3.2, p. 9 (in the proof of Lemma 1). Let `k ≥ 2` and assume Lemma 1 for tokens `1, …, k − 1`. If token `k` departs from `v = tail e` along the edge `e` of `Gζ` at time `s` right after a token `h < k` departed along `e` (at time `s − 1`), then `s ≤ r0 + (L_{oζdζ} − L_{vdζ} + k − 1)`, written additively. -/
theorem claim_1 {V E ι : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (N : Network V E) (hN : N.Acyclic) (R : RunData ι E V) (hR : IsADR N R) (ζ : ι) (r0 : ℕ) (hr0 : R.entry ζ ≤ r0) (hinside : R.inside ζ r0) (k : ℕ) (hk : 2 ≤ k) (IH : ∀ h : ℕ, 1 ≤ h → h < k → DepartBound N R ζ r0 h) (e : E) (he : e ∈ Gz N R ζ) (s : ℕ) (hks : tokAt R ζ r0 s k = some e) (hkdep : tokAt R ζ r0 (s + 1) k ≠ some e) (hprev : ∃ h : ℕ, 1 ≤ h ∧ h < k ∧ 1 ≤ s ∧ tokAt R ζ r0 (s - 1) h = some e ∧ tokAt R ζ r0 s h ≠ some e) : s + N.longest (N.tail e) (R.dest ζ) + 1 ≤ r0 + N.longest (R.orig ζ) (R.dest ζ) + k := by sorry

end AtomicDynRouting.ResidenceTime
