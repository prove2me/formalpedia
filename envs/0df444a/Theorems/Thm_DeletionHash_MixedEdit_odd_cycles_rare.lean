-- Prove2me | Theorems.Thm_DeletionHash_MixedEdit_odd_cycles_rare
-- name    : DeletionHash.MixedEdit.odd_cycles_rare
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:10.452327+00:00
-- url     : https://prove2.me/theorems/fd1c0fb4-c334-4ff6-acfe-e0dbef5563a7
-- title:
--   Proposition 6.1 — odd cycles rare
-- statement:
--   For every $t\ge2$, $b\ge1$, the constants in §6.1 may be chosen uniformly in the alphabet: an integer $a\ge1$ satisfies the entire generating-set estimate of Lemma 5.1, and there are integers $\lambda\ge2$ and $L_0\ge1$, depending only on $t,b$, such that
--   $$(2tR+1)(LR)^{aR}\le L^{\lambda R}\quad\text{for all }L\ge L_0,\ 2\le R\le M.$$
--   For every alphabet of size $q\ge2$, all parameters in the standing regime with $L\ge L_0$, and $r\ge1$, if
--   $$2^r\ge4q^{6bt+1}n^{2t-1}L^\lambda,$$
--   then each $x\in W_{n,k}$ satisfies
--   $$\Pr_H[x\notin E\text{ and its component in }\Gamma_H\text{ is not bipartite}]\le1/12.$$
--   This is the unconditional intersection event and is false when $x$ is discarded. The counting estimate and valid constant choices are conclusions, not oracle hypotheses; the explicit $L_0$ retains the eventual regime of equation (6).
--
--   Differences from the source:
--   - encoding: the standing assumptions of §§2.2–6 → Regime: q≥2, t≥2, b≥1, k=2 ceil(log_q n)+2, L=3(k+b+1), b<k, L≤n; reason: the section preamble is explicit in each applicable signature
--   - encoding: the choices a_{t,b}, λ_{t,b} and the sufficiently-large-L convention in §6.1 → existential a, λ, L₀ before q, with the counting estimate and equation (6) as conclusions; reason: this closes the proposition over the valid source choices without assuming an unproved counting theorem or choosing constants separately for each alphabet
--   - encoding: x∉E and its component is non-bipartite → BadComponent includes surviving-vertex membership and failure of a component two-colouring; reason: the event is false off the graph and no conditional probability is substituted
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Proposition 6.1, printed p. 18 (PDF p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf; standing constant choices: §6.1, equation (6), printed p. 18 (PDF p. 20)

import Definitions.Def_DeletionHash_MixedEdit_Generation
import Definitions.Def_DeletionHash_MixedEdit_ConflictGraph

namespace DeletionHash.MixedEdit

universe u

/-- Proposition 6.1 with the alphabet-uniform choices and eventual-L regime of §6.1.
The counting estimate is a conclusion here, not an assumed oracle for a selected exponent. -/
theorem odd_cycles_rare (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) :
    ∃ a : ℕ, 1 ≤ a ∧ (∀ (q : ℕ) (α : Type u) [Fintype α] [DecidableEq α],
      Fintype.card α = q → ∀ n k L : ℕ, Regime q n t b k L →
      ∀ x : Word α n, IsUnique k (letters x) → ∀ R c : ℕ, 1 ≤ R → c ≤ 2*t*R →
      generatingCount k t b (spectrum L (letters x)) R c ≤
        ((n^c * q^(6*b*t*R) * (L*R)^(a*R) : ℕ) : ℕ∞)) ∧
    ∃ lam L₀ : ℕ, 2 ≤ lam ∧ 1 ≤ L₀ ∧
      (∀ L : ℕ, L₀ ≤ L → ExponentBound t b a lam L) ∧
      ∀ (q : ℕ) (α : Type u) [Fintype α] [DecidableEq α], Fintype.card α = q →
        ∀ n k L r : ℕ, Regime q n t b k L → L₀ ≤ L → 1 ≤ r →
        4*q^(6*b*t+1)*n^(2*t-1)*L^lam ≤ 2^r →
        ∀ x : Word α n, IsUnique k (letters x) →
        uniformProbability (fun ξ : HashSample α L r => BadComponent n k t b ξ x) ≤ (1:ℝ)/12 := by sorry

end DeletionHash.MixedEdit
