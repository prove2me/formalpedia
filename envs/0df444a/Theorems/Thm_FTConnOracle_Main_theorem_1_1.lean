-- Prove2me | Theorems.Thm_FTConnOracle_Main_theorem_1_1
-- name    : FTConnOracle.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:28:45.334464+00:00
-- url     : https://prove2.me/theorems/6ea0922e-a3ff-4316-85d1-8da9d4d44916
-- title:
--   Theorem 1.1 — deterministic component oracles with Õ(min{f^{2/5}, n^{3/4}}·n) bits, Õ(n^{7/4}) for unrestricted failures, n^{o(1)} more in polynomial time
-- statement:
--   There are universal constants $C>0$ and $k\in\mathbb N$ such that the following three statements hold.
--
--   1. For every $n\ge2$ and every integer $1\le f\le\binom n2$ there is a deterministic component oracle on $[n]$ for at most $f$ failures using $b$ bits, where
--   $$b\ \le\ C\cdot\min\{f^{2/5},n^{3/4}\}\cdot n\cdot\log(2n)^k:$$
--   an encoder $\mathrm{Enc}:\{\text{graphs on }[n]\}\to\{0,1\}^b$ and a decoder $\mathrm{Dec}$ that sees only $\mathrm{Enc}(G)$ and $F$, with $\mathrm{Dec}(\mathrm{Enc}(G),F)=\mathrm{cc}(G-F)$ for every simple graph $G$ on $[n]$ and every $F\subseteq E(G)$ with $|F|\le f$.
--   2. For every $n\ge2$ there is a deterministic component oracle using $m\le C\,n^{7/4}\log(2n)^k$ bits that supports failure sets of arbitrary size: $\mathrm{Dec}(\mathrm{Enc}(G),F)=\mathrm{cc}(G-F)$ for every $G$ and every $F\subseteq E(G)$.
--   3. (Polynomial time.) There are $h:\mathbb N\to\mathbb R$ with $h(n)\to0$ and one polynomial-time encoder $E$ such that for every $n\ge2$ and integer $1\le f\le\binom n2$ there is a decoder $\mathrm{Dec}_{n,f}$ with, for every graph $G$ on $[n]$,
--   $$|E(n,f,G)|\ \le\ \min\{f^{2/5},n^{3/4}\}\cdot n^{1+h(n)}$$
--   and $\mathrm{Dec}_{n,f}(E(n,f,G),F)=\mathrm{cc}(G-F)$ for every $F\subseteq E(G)$ with $|F|\le f$.
--
--   This answers whether deterministic fault-tolerant connectivity oracles admit subquadratic space: they do, even for unrestricted failures, while Theorem 1.2 shows they need polynomially more space than randomized ones.
--
--   **Formalization Note.** Clause 2 uses the published `DetConnSketch.Main.CompProtocol (Fin n) m`, whose deletion graph $G_B\le G_A$ is the failure set $F\subseteq E(G)$. The input of $E$ is $(1^n,1^f,\text{adjacency bits of }G)$, and polynomial time is the published `LowErrExt.IsPolyTime`.
--
--   Differences from the source:
--   - encoding: Õ(min{f^{2/5}, n^{3/4}} n) and Õ(n^{7/4}) bits → b ≤ C·min{f^{2/5}, n^{3/4}}·n·log(2n)^k and m ≤ C·n^{7/4}·log(2n)^k with universal C > 0 and k ∈ ℕ quantified before n and f; reason: standard meaning of Õ(·) with absolute constants; log(2n) ≥ log 4 > 1 so small n are absorbed
--   - encoding: a deterministic connectivity oracle using b bits that reports the connected-component partition of G − F for every F ⊆ E(G) with |F| ≤ f → FTOracle n f b: enc : SimpleGraph (Fin n) → (Fin b → Bool), dec : (Fin b → Bool) → Finset (Sym2 (Fin n)) → (Fin n → Fin n → Prop), dec (enc G) F = (G − F).Reachable for all F ⊆ E(G), |F| ≤ f; for arbitrary failure sets DetConnSketch.Main.CompProtocol (Fin n) m; reason: the paper's model (§2, §2.1): Dec sees only Enc(G) and F, correctness only on valid queries, space = number of bits of the encoding; CompProtocol's GB ≤ GA is exactly F ⊆ E(G)
--   - reading: Obtaining the oracle in polynomial time introduces an extra factor of n^{o(1)} in the space bounds → one encoder E with LowErrExt.IsPolyTime E on input (1^n, 1^f, adjacency bits of G), output length ≤ min{f^{2/5}, n^{3/4}}·n^{1+h(n)} with one h → 0 fixed before n and f, and a decoder Dec_{n,f} seeing only the output and F; reason: the paper names no machine model; polynomial time = one uniform Turing machine; n^{o(1)} = n^{h(n)} with h → 0, which also absorbs the constant and the polylog factor of Õ; f = C(n,2) covers the arbitrary-failure bound n^{7/4+o(1)}
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), p. 3 (PDF 5), Theorem 1.1

import Mathlib
import Definitions.Def_FTConnOracle_Main_Oracle
import Definitions.Def_FTConnOracle_Main_Codes
import Definitions.Def_DetConnSketch_Main_Protocol
import Definitions.Def_LowErrExt_IsPolyTime

open Filter Topology

namespace FTConnOracle.Main

/-- Theorem 1.1 (p. 3). There are universal constants `C > 0` and `k ∈ ℕ` such that
(i) for every `n ≥ 2` and integer `1 ≤ f ≤ C(n,2)` there is a deterministic component oracle on
`[n]` for at most `f` failures with `b ≤ C · min{f^{2/5}, n^{3/4}} · n · log(2n)^k` bits;
(ii) for every `n ≥ 2` there is a deterministic component oracle for failure sets of arbitrary
size (`DetConnSketch.Main.CompProtocol`) with `m ≤ C · n^{7/4} · log(2n)^k` bits;
(iii) there are `h : ℕ → ℝ` with `h(n) → 0` and one polynomial-time encoder that, on the input
code of `(n, f, G)`, outputs at most `min{f^{2/5}, n^{3/4}} · n^{1 + h(n)}` bits from which a
decoder (depending on `n, f` only) recovers `cc(G − F)` for every `F ⊆ E(G)` with `|F| ≤ f`. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
      (∀ n f : ℕ, 2 ≤ n → 1 ≤ f → f ≤ n.choose 2 →
        ∃ b : ℕ,
          (b : ℝ) ≤ C * min ((f : ℝ) ^ ((2 : ℝ) / 5)) ((n : ℝ) ^ ((3 : ℝ) / 4)) * (n : ℝ) *
            Real.log (2 * (n : ℝ)) ^ k ∧
          Nonempty (FTOracle n f b)) ∧
      (∀ n : ℕ, 2 ≤ n →
        ∃ m : ℕ,
          (m : ℝ) ≤ C * (n : ℝ) ^ ((7 : ℝ) / 4) * Real.log (2 * (n : ℝ)) ^ k ∧
          Nonempty (DetConnSketch.Main.CompProtocol (Fin n) m)) ∧
      (∃ h : ℕ → ℝ, Tendsto h atTop (𝓝 0) ∧
        ∃ E : List (List Bool) → List Bool, LowErrExt.IsPolyTime E ∧
          ∀ n f : ℕ, 2 ≤ n → 1 ≤ f → f ≤ n.choose 2 →
            ∃ Dec : List Bool → Finset (Sym2 (Fin n)) → (Fin n → Fin n → Prop),
              ∀ G : SimpleGraph (Fin n),
                ((E (oracleInput f G)).length : ℝ) ≤
                    min ((f : ℝ) ^ ((2 : ℝ) / 5)) ((n : ℝ) ^ ((3 : ℝ) / 4)) *
                      (n : ℝ) ^ (1 + h n) ∧
                ∀ F : Finset (Sym2 (Fin n)), F ⊆ edges G → F.card ≤ f →
                  Dec (E (oracleInput f G)) F = (removeEdges G F).Reachable) := by sorry

end FTConnOracle.Main
