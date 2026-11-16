-- Prove2me | Theorems.Thm_ExplicitTensorBarrier694_Explicit_Supplement_lemma_5_3
-- name    : ExplicitTensorBarrier694.Explicit.Supplement.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:42:10.94575+00:00
-- url     : https://prove2.me/theorems/f25ce349-a8cb-49ca-a780-75b2277e308b
-- title:
--   Lemma 5.3 — $\sum_{i\in S}\Delta_{S\setminus\{i\}}^2f'(i)=0$ for $f$ vanishing on $S$
-- statement:
--   Let $p\ge1$ and $n=2p+1$, and write $[n]=\{1,\dots,n\}$. For $S\subseteq[n]$ let $\Delta_S=\prod_{i<j,\ i,j\in S}(j-i)$ (empty product $1$). If a complex polynomial $f$ of degree less than $n$ vanishes at every point of a $(p+1)$-element subset $S\subseteq[n]$, then
--
--   $$\sum_{i\in S}\Delta_{S\setminus\{i\}}^2\,f'(i)=0,$$
--
--   where $f'$ is the derivative of $f$.
--
--   This interpolation identity is used in the proof of Theorem 5.2. This is a paper-proved result awaiting a formal proof.
--
--   Differences from the source:
--   - encoding: ℂ[t]_{<n} → Polynomial.degreeLT ℂ (2p+1); reason: the same space; the zero polynomial is included
--   - encoding: (p+1)-subsets S ⊆ [n] → S : Finset ℕ with S ⊆ Icc 1 (2p+1) and card S = p+1; reason: the same sets of integers, used as complex evaluation points
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), Lemma 5.3, p.16; standing context of §5 and Δ_S, p.15 (PDF same); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Supplement_OddWitness

open scoped BigOperators
open Polynomial

namespace ExplicitTensorBarrier694.Explicit.Supplement

/-- Lovitz, STOC 2027 submission #694 (October 2026), Lemma 5.3, p.16 (standing context
of §5, p.15: n = 2p+1 ≥ 3, [n] = {1,…,n}). If f ∈ ℂ[t]_{<n} vanishes on a (p+1)-subset
S ⊆ [n], then Σ_{i∈S} Δ²_{S∖{i}} f′(i) = 0. -/
theorem lemma_5_3 (p : ℕ) (hp : 1 ≤ p) (f : ℂ[X])
    (hf : f ∈ Polynomial.degreeLT ℂ (2 * p + 1))
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 (2 * p + 1)) (hcard : S.card = p + 1)
    (hvan : ∀ i ∈ S, f.eval (i : ℂ) = 0) :
    ∑ i ∈ S, vandermondeDelta (S.erase i) ^ 2 * (derivative f).eval (i : ℂ) = 0 := by sorry

end ExplicitTensorBarrier694.Explicit.Supplement
