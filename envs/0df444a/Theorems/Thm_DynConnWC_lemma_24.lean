-- Prove2me | Theorems.Thm_DynConnWC_lemma_24
-- name    : DynConnWC.lemma_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:41:43.685648+00:00
-- url     : https://prove2.me/theorems/2524338f-340a-4b52-9161-c320e2fac74a
-- title:
--   Lemma 24 — resources on every tape, and the program implements the algorithm
-- statement:
--   For fixed $d,\beta>0$ there are a program $P$ of the online randomized word RAM and constants $C,c_0$ such that for all $n\ge2$ and $W\ge c_0\lceil\log_2n\rceil$ there are a setup $S$ of the algorithm and a map $\rho$ from tapes to random choices with the following properties. $S$ uses the plain search, meets the standing assumptions and meets the budget (2)–(5) for $T_0=\lceil n^d\rceil$, $\delta=n^{-\beta}$; $\rho$ pushes the tape law to the uniform law. On every tape $\omega$ and every valid operation sequence of any length:
--
--   1. $P$ reaches every read, and its answers equal those of the algorithm with random choices $\rho(\omega)$.
--   2. Initialization takes at most $Cn\log_2^2n$ steps, each update at most $C\log_2^3n$, and each query at most $C\max(1,\log_2n/\log_2\log_2n)$.
--   3. Every memory cell touched is below $Cn\log_2^2n$.
--
--   This is what Theorem 1 rests on for "these bounds always hold".
--
--   Differences from the source:
--   - reading: the data structure, with no statement connecting it to the algorithm → an existential program, setup and map $\rho$, with its answers equal to the algorithm's; reason: Lemma 24 bounds the implementation of §§3.5–3.7 and Appendices A–B, and without this clause it could not feed Theorem 23 into Theorem 1
--   - reading: the parameters chosen in §4.6 → parameters meeting the budget (2)–(5); reason: the budget is all the analysis uses, and for an uncomputable real $d$ no fixed program can compute $\lceil n^d\rceil$ exactly, so the exact ceilings would make the statement false; §4.6 says the choices suffice and says $k,h,r,w=O(\log n)$
--   - generalization: words of $\Theta(\log n)$ bits → every $W\ge c_0\lceil\log_2n\rceil$; reason: a program that works for all larger $W$ specializes to the source's word size
--   - encoding: $O(\cdot)$ with constants depending on $d,\beta$ → $C,c_0$ chosen after $d,\beta$ and before $n,W$; reason: this is the meaning of the hidden constants
--   - encoding: $O(\log n/\log\log n)$ query time → $C\max(1,\log_2n/\log_2\log_2n)$; reason: $\log_2\log_22=0$, and Lean's division by zero would give $0$ at $n=2$; the maximum is inert for $n\ge4$
--   - reading: $O(n\log^2n)$ words → every memory cell touched is below $Cn\log_2^2n$; reason: space in words is measured by the addresses used
--   - reading: regardless of the random choices → on every tape and every valid sequence of any length; reason: nothing in the algorithm depends on the update count (p.17, p.24)
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Lemma 24, p.24 (PDF 25); §4.6, p.23 (PDF 24); §2, p.4 (PDF 5)

import Mathlib
import Definitions.Def_DynConnWC_Bounds

set_option autoImplicit false

namespace DynConnWC

/-- **Lemma 24 (Resources).** King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027 submission, sha256 9d16c13e…), p.24 (PDF 25).
"Regardless of the random choices, each update takes O(log³ n) worst-case time, each query takes
O(log n/ log log n) worst-case time, the data structure uses O(n log² n) words, and initialization
takes O(n log² n) time."

**Formalization Note.** The lemma bounds the implementation of §§3.5–3.7 and Appendices A–B, so its
form says what that implementation is: for fixed `d, β` there are one program and constants `C, c₀`
such that, for all `n ≥ 2` and word sizes `W ≥ c₀⌈log₂ n⌉`, there are a setup `S` (plain search,
standing assumptions, budget (2)–(5) for `T0 = ⌈n^d⌉`, `δ = n^{−β}`) and a map `ρ` from tapes to random
choices that pushes the tape law to the uniform law, with the following on every tape and every valid
sequence of any length: the program answers as the algorithm does for `R = ρ ω`, and the resource
bounds hold. -/
theorem lemma_24 (d β : ℝ) (hd : 0 < d) (hβ : 0 < β) :
    ∃ (P : Program) (C c₀ : ℕ), ∀ n, 2 ≤ n → ∀ W, c₀ * Nat.clog 2 n ≤ W →
      ∃ (S : AlgSetup n) (ρ : (ℕ → Fin (2 ^ W)) → RandChoices S),
        S.mode = .plain ∧ S.Wf ∧ Budget S (T0par n d) (deltaPar n β) ∧ PushesToUniform W S ρ ∧
        ∀ (ω : ℕ → Fin (2 ^ W)) (σ : List (Op n)), Valid σ →
          Implements W P n ω σ S (ρ ω) ∧ TimeBounds C W P n ω σ ∧ SpaceBound C W P n ω σ := by sorry

end DynConnWC
