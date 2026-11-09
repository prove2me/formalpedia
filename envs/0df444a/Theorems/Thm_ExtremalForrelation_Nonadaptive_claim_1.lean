-- Prove2me | Theorems.Thm_ExtremalForrelation_Nonadaptive_claim_1
-- name    : ExtremalForrelation.Nonadaptive.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:37.929538+00:00
-- url     : https://prove2.me/theorems/39e8f143-c844-42f4-ad96-d22bb34bf7fe
-- title:
--   Claim 1 — queried cosets have many unqueried neighbours
-- statement:
--   Throughout, $n$ is a multiple of $4$, $m=n/2$ and $M=2^m$ (the paper's standing notation, p. 3).
--
--   Fix a query set $Q$ with $q=|Q|$, a subspace $K$ with $\dim K=m$ that is $r$-good for $Q$ (for an integer $r\ge1$), and a transcript $\tau$ with $\rho(\tau\mid K)>0$; let $H=H_\tau$ be its pinning graph.
--   Then
--   $$\big|\{j\notin G:(i,j)\in H\}\big|\ge \frac{M}{2^r}-q\quad\text{for all }i\in F,\qquad \big|\{i\notin F:(i,j)\in H\}\big|\ge\frac{M}{2^r}-q\quad\text{for all }j\in G. \tag{19}$$
--
--   This degree bound drives the switching argument of Claim 2.
--
--   Differences from the source:
--   - encoding: 'for K, H and τ as above' (K r-good, H the pinning graph of τ with ρ(τ | K) > 0) → hypotheses IsGood Q r K with 1 ≤ r, 0 < ρ(τ | K), and H written as pinGraph Q K τ; reason: the inherited setting of Lemma 10, stated explicitly
--   - reading: 'K, H and τ as above' may or may not carry Lemma 10's further hypothesis q ≤ M/2^{r+3} → no bound on q is assumed; reason: the stronger reading; Claim 1 names only K, H and τ, and with the bound added the Lean statement specializes to the other reading
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), Claim 1 (in the proof of Lemma 10), p. 18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Pinning
import Definitions.Def_ExtremalForrelation_Nonadaptive_Algorithm

open Classical

namespace ExtremalForrelation.Nonadaptive

/-- Claim 1 (p. 18), in the setting of Lemma 10 (`K` is `r`-good, `H = H_τ` with `ρ(τ | K) > 0`):
`|{j ∉ G : (i, j) ∈ H}| ≥ M/2^r − q` for all `i ∈ F`, and
`|{i ∉ F : (i, j) ∈ H}| ≥ M/2^r − q` for all `j ∈ G` (equation (19)). -/
theorem claim_1 {n : ℕ} (hn : 4 ∣ n) (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n))
    (hK : Module.finrank (ZMod 2) K = n / 2) (r : ℕ) (hr : 1 ≤ r) (hgood : IsGood Q r K)
    (τ : Transcript Q) (hτ : 0 < rhoK Q K τ) :
    (∀ C ∈ Fset Q K, (2 : ℝ) ^ (n / 2) / 2 ^ r - Q.card ≤
      ((Finset.univ.filter (fun D : V n ⧸ orth K =>
        D ∉ Gset Q K ∧ pinGraph Q K τ C D)).card : ℝ)) ∧
    (∀ D ∈ Gset Q K, (2 : ℝ) ^ (n / 2) / 2 ^ r - Q.card ≤
      ((Finset.univ.filter (fun C : V n ⧸ K =>
        C ∉ Fset Q K ∧ pinGraph Q K τ C D)).card : ℝ)) := by sorry

end ExtremalForrelation.Nonadaptive
