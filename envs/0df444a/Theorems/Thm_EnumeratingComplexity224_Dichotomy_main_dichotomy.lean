-- Prove2me | Theorems.Thm_EnumeratingComplexity224_Dichotomy_main_dichotomy
-- name    : EnumeratingComplexity224.Dichotomy.main_dichotomy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:30:49.185376+00:00
-- url     : https://prove2.me/theorems/84af2ff2-d1d0-478d-a8fc-98c78e069e0e
-- title:
--   Theorem 1 — main dichotomy for enumerating complexity
-- statement:
--   Fix optimal deterministic, randomized and conditional randomized enumerators, defining $D$, $R$ and conditional $R$, respectively. There is one finite real $d>0$, depending only on these fixed machines, such that for all natural $k,l$ and every $S\subseteq\mathbb N$ with $R(S)\ge2^{-k}$,
--   $$D(S)\le l\quad\text{or}\quad
--   \exists F\subseteq S\text{ finite},\quad D(F)>l\ \text{and}\ R(F\mid k,l)\ge\frac{2^{-k}}d.$$
--   The finite witness and both its inequalities are quantified together, after $S$. The constant is chosen before $k,l,S$; the conditional machine receives the auxiliary string $\langle k\rangle l$, not an instance-dependent new description. Both finite and infinite sets are included, as are $k=0$ and $l=0$. No computable-enumerability hypothesis is imposed. The result identifies a hard finite subset with comparable conditional enumeration probability whenever the entire set has no description of length at most $l$.
--
--   The source's proof supplies $d=\max(4/c_N,1/c)$ from its positive machine-domination constants; no machine-independent numeral is asserted.
--
--   Differences from the source:
--   - encoding: Turing machines with finite padded binary inputs and non-halting output → finite partial-recursive instruction codes with padded cell reads, a sequential fair-bit interface and append-only natural-number messages; D takes values in the extended naturals and probabilities are extended nonnegative reals; reason: the interpreter gives effective finite simulations and the same infinite enumerations; program length is still the exact binary input length
--   - generalization: fixed optimal machines and the p.6 convention D(S)>0 and R(S)≤1/4 when using logarithmic bounds → arbitrary fixed optimal machines, without the logarithmic normalization; reason: the p.6 convention sets aside finitely many exceptional sets to make logarithms defined; the selected logarithm-free source arguments apply to all optimal machine choices and all their sets
--   - encoding: the auxiliary string ⟨k⟩l with binary naturals and a self-delimiting first component → little-endian binary with zero [false], unary binary-length prefix for k, and a padded end marker after l; reason: this is a computable prefix-decodable convention with first-component length 2 log₂ k+O(1); it changes no pair instance
-- source:
--   Alexander Shekhovtsov, Nikolay Vereshchagin, Georgii Zakharov, Enumerating Complexity Revisited, STOC 2027 submission #224 (October 2026), p. 2, Theorem 1 (Main dichotomy); proof pp.7–11

import Definitions.Def_EnumeratingComplexity224_Dichotomy_Machines

namespace EnumeratingComplexity224.Dichotomy

/-- Full Theorem 1, p.2. The positive finite constant is uniform in k,l,S.
No computable-enumerability hypothesis or finiteness restriction on S. -/
theorem main_dichotomy (m p q : Machine)
    (hm : OptimalDeterministic m) (hp : OptimalRandom p) (hq : OptimalConditional q) :
    ∃ d : ℝ, 0 < d ∧ ∀ (k l : ℕ) (S : Set ℕ),
      ENNReal.ofReal (dyadic k) ≤ probability p S [] →
      complexity m S ≤ (l : ℕ∞) ∨
      ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ S ∧
        (l : ℕ∞) < complexity m (↑F : Set ℕ) ∧
        ENNReal.ofReal (dyadic k / d) ≤ probability q (↑F : Set ℕ) (pairInput k l) := by sorry

end EnumeratingComplexity224.Dichotomy
