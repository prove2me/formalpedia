-- Prove2me | Theorems.Thm_EditPRC_Boost_theorem_3_12
-- name    : EditPRC.Boost.theorem_3_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:09:32.691956+00:00
-- url     : https://prove2.me/theorems/970754b5-0860-4bfb-ac48-18472146107a
-- title:
--   Theorem 3.12 (= Theorem 1.5) — a low-rate edit-robust PRC over $\Sigma$ gives a constant-rate edit-robust PRC over $\Sigma\times\Gamma$
-- statement:
--   Let $\Sigma$ be a finite nonempty alphabet, $\varepsilon_E>0$ and $0<c<1$. Suppose there is a secret-key pseudorandom code $P$ in the sense of Definition 2.1 (polynomial-time KeyGen, Enc, Dec with Dec defined on all of $\Sigma^\star$; negligible advantage for every polynomial-time distinguisher with oracle access to $\mathrm{Enc}_{\mathrm{sk}}(\cdot)$ versus a fresh uniform string per call; negligible soundness error) with some finite message alphabet $M$ and codeword alphabet $\Sigma$, such that
--   1. its blocklength is $n(\lambda)=\lambda$;
--   2. its unnormalized rate is at least $n^c$: $k(\lambda)\log|M|\ \ge\ n(\lambda)^c\log|\Sigma|$ for all sufficiently large $\lambda$;
--   3. it is strongly-adaptively robust to an $\varepsilon_E$ fraction of edits: with probability $1-\mathrm{negl}(\lambda)$ over the key and the encoding of any message $m$, $\mathrm{Dec}_{\mathrm{sk}}(x')=m$ for **every** $x'$ with $D_E(x,x')\le\varepsilon_E|x|$ (insertions, deletions and substitutions).
--
--   Then there exist a finite nonempty alphabet $\Gamma$, constants $\varepsilon'_E>0$ and $r'>0$, a finite message alphabet $M'$ and a pseudorandom code $P'$ in the same sense, with codeword alphabet $\Sigma\times\Gamma$ and blocklength $n'(\lambda)=\lambda$, that is strongly-adaptively robust to an $\varepsilon'_E$ fraction of edits and has constant rate:
--   $$\frac{k'(\lambda)\log|M'|}{\lambda\,\log|\Sigma\times\Gamma|}\ \ge\ r'\qquad\text{for all sufficiently large }\lambda .$$
--   The alphabet $\Gamma$ and the constants $\varepsilon'_E,r'$ are fixed before $\lambda$; they may depend on $\Sigma$, $\varepsilon_E$, $c$ and $P$.
--
--   This is the paper's black-box boost: any edit-robust PRC of inverse-polynomial rate becomes one of constant rate over a constant-size alphabet, the first such construction for edit errors. Applied to a low-rate edit-robust PRC under the permuted codes assumption it gives the paper's existence result (Theorem 1.7), which is not part of this mission.
--
--   Differences from the source:
--   - reading: "PRC" (no security level stated) → a PRC of Definition 2.1 on both sides: polynomial-time algorithms, negligible advantage against polynomial-time oracle distinguishers, negligible soundness and robustness errors; reason: the theorem names no security level, and Definition 2.1 is the paper's definition of a PRC.
--   - reading: "$\mathrm{Dec}:\{0,1\}^{\kappa(\lambda)}\times\Sigma^{n(\lambda)}\to\Gamma^{k(\lambda)}\cup\bot$" (syntax), while soundness quantifies over $y\in\Sigma^\star$ and edits change the length → Dec takes every finite string over the codeword alphabet; reason: edit robustness and soundness on $\Sigma^\star$ are meaningless otherwise.
--   - reading: Dec "randomized" in the tuple of Definition 2.1 → Dec deterministic; reason: the soundness and robustness probabilities are printed over KeyGen and Enc only, and strongly-adaptive robustness holds "even after fixing the randomness of the secret key and encoding".
--   - reading: soundness "for any fixed $y\in\Sigma^\star$, $\Pr\ge1-\mathrm{negl}(\lambda)$" → one negligible function for all $y$; robustness "for any $m\in\Gamma^{k(\lambda)}$" → one negligible function for all $\lambda$ and $m$; reason: $m$ ranges over a set that changes with $\lambda$, and the proof's soundness bound does not depend on $y$.
--   - reading: blocklength $n$ → $n(\lambda)=\lambda$ in hypothesis and conclusion; reason: the paper assumes $\lambda=n$ throughout (p. 10).
--   - generalization: "(unnormalized) rate $n^c$" → $k(\lambda)\log|M|\ge n(\lambda)^c\log|\Sigma|$ for all large $\lambda$; reason: unnormalized rate is $n$ times the relative rate (p. 8, Proposition 3.6); the hypothesis admits every code of unnormalized rate exactly $n^c$ (and, since $c$ is arbitrary, every code of rate $\Omega(n^c)$), so the theorem specializes to the source's; exact equality is in general not attainable with integer $k$.
--   - reading: "$\varepsilon_E$-edit-robust" → robust to the ball $B_E(x,\varepsilon_E)=\{x':D_E(x,x')\le\varepsilon_E|x|\}$ with $\varepsilon_E>0$; reason: the notation of p. 8; an edit-robust code corrects a positive fraction.
--   - reading: "constant rate", "$\Gamma$ of constant size" → relative rate $\ge r'>0$ for all large $\lambda$, with $\Gamma$ a fixed finite nonempty type and $\varepsilon'_E>0$, $r'$, $\Gamma$ chosen before $\lambda$; reason: the meaning of "constant" for a code family (p. 8).
--   - encoding: machines → multi-stack Turing machines on bit encodings with the coins as an extra input and $1^\lambda$ in every input; distinguishers → oracle algorithms whose $i$-th call is answered with its own independent randomness (`EditPRC.Boost.Machine`); reason: Lean convention for "polynomial-time randomized algorithm" and for an oracle with fresh randomness per call.
--   - encoding: negligible functions → `QuantumPRC.Negligible`; edit distance → `OAI.EditDistortion.edit`; message alphabets → existentially quantified finite nonempty types; $\Sigma$ nonempty; reason: Lean conventions; an empty alphabet admits no code.
--
--   **Formalization Note.** The message alphabet of Definition 2.1 is written $M$ here because Theorem 3.12 uses $\Gamma$ for the synchronization alphabet. Robust soundness, local decodability and noise robustness are not part of the statement.
-- source:
--   Gozon, Edit-Robust Pseudorandom Codes, Watermarks, and Steganography, STOC 2027 submission (manuscript sha256 73170029…6b60), p. 24, Theorem 3.12 (informal Theorem 1.5, p. 4); Definition 2.1, p. 9; notation p. 8; λ = n, p. 10

import Mathlib
import Definitions.Def_EditPRC_Boost_PRC

open Filter

namespace EditPRC.Boost

/-- **Theorem 3.12 (Constant-rate edit PRC boost) = Theorem 1.5.** Let `S` (the paper's `Σ`) be
a finite alphabet, `ε_E > 0` and `0 < c < 1`. Suppose some secret-key PRC `P` (Definition 2.1)
with codeword alphabet `S`, blocklength `n(λ) = λ` and unnormalized rate at least `n^c` is
strongly-adaptively robust to an `ε_E` fraction of edits. Then there are a finite alphabet `Γ`,
constants `ε'_E > 0`, `r' > 0`, and a PRC `P'` (Definition 2.1) with codeword alphabet `S × Γ`,
blocklength `n(λ) = λ` and relative rate at least `r'` for all large `λ`, that is
strongly-adaptively robust to an `ε'_E` fraction of edits. -/
theorem theorem_3_12 (S : Type) [Fintype S] [Nonempty S] (εE c : ℝ) (hεE : 0 < εE)
    (hc0 : 0 < c) (hc1 : c < 1)
    (hP : ∃ (M : Type) (_ : Fintype M) (_ : Nonempty M) (P : PRC M S),
      P.IsPRC ∧ P.EditRobust εE ∧ (∀ lam, P.blockLen lam = lam) ∧
      ∀ᶠ lam in atTop,
        ((P.blockLen lam : ℝ) ^ c) * Real.log (Fintype.card S) ≤
          (P.msgLen lam : ℝ) * Real.log (Fintype.card M)) :
    ∃ (Γ : Type) (_ : Fintype Γ) (_ : Nonempty Γ) (ε' r' : ℝ), 0 < ε' ∧ 0 < r' ∧
      ∃ (M' : Type) (_ : Fintype M') (_ : Nonempty M') (P' : PRC M' (S × Γ)),
        P'.IsPRC ∧ P'.EditRobust ε' ∧ (∀ lam, P'.blockLen lam = lam) ∧
        ∀ᶠ lam in atTop, r' ≤ P'.relRate lam := by sorry

end EditPRC.Boost
