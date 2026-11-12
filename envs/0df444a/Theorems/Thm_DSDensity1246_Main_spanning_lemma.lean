-- Prove2me | Theorems.Thm_DSDensity1246_Main_spanning_lemma
-- name    : DSDensity1246.Main.spanning_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:11:08.801893+00:00
-- url     : https://prove2.me/theorems/7d949649-0ea8-4c7c-bac6-1aed3d7d04be
-- title:
--   Lemma 2.1 — Spanning Lemma [HMMS26]
-- statement:
--   Let $k,n$ be natural numbers, let $[k]=\{1,\ldots,k\}$, and let $W\subseteq[k]^n$ be any hypothesis class, including the empty class. Let $\ell\ge1$ and let $s$ be any natural number at least its $\ell$-DS dimension $d^\ell_{\rm DS}(W)$. Write $V_W$ for all real-valued functions on $W$, and $M_s^\ell(W)$ for the evaluated monomials with each exponent less than $k$ and at most $s$ exponents at least $\ell$. Then
--
--   $$\operatorname{span}_{\mathbb R}M_s^\ell(W)=V_W.$$
--
--   This is the algebraic spanning statement attributed to [HMMS26] in the submission. It supplies the sole numbered dependency of the maximum-density theorem. It does not assume spanning, a basis, a full box, or a one-neighbor specialization.
--
--   Differences from the source:
--   - encoding: coordinates [n] and labels [k] = {1,…,k} → coordinates Fin n and labels Fin k evaluated as val + 1 in ℝ; reason: bijective reindexing preserves every source instance and its monomial evaluations
--   - encoding: s ≥ d^ℓ_DS(W) and spanning all real functions on W → listDSDim ℓ W ≤ (s : ℕ∞) and Submodule.span ℝ (monomials ℓ s W) = ⊤ in W → ℝ; reason: the extended-natural comparison is the same finite upper bound; top is the entire pointwise real function space
-- source:
--   Chirag Pabbaraju, STOC 2027 submission #1246 (October 2026), p. 8, Lemma 2.1 (Spanning Lemma [HMMS26])

import Definitions.Def_DSDensity1246_Main_dsModel
import Definitions.Def_DSDensity1246_Main_monomials

namespace DSDensity1246.Main

/-- Lemma 2.1 (Spanning Lemma [HMMS26]), p. 8, at full list-size generality. -/
theorem spanning_lemma (k n ℓ s : ℕ) (W : Set (Fin n → Fin k))
    (hℓ : 1 ≤ ℓ) (hs : listDSDim ℓ W ≤ (s : ℕ∞)) :
    Submodule.span ℝ (monomials ℓ s W) = ⊤ := by sorry

end DSDensity1246.Main
