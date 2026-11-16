-- Prove2me | Theorems.Thm_AcceptSubcube_Supplement_theorem_4_8
-- name    : AcceptSubcube.Supplement.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:51:37.717683+00:00
-- url     : https://prove2.me/theorems/7320b001-0f4a-4ed1-9387-69e9ba6c69fb
-- title:
--   Theorem 4.8 — deterministic round-or-cut repair: $C_{\mathcal I}(\hat x)\le130\,\mathrm{OPT}_{\tau,r}+\tilde K_kD_3(n)r^3$
-- statement:
--   Fix $k\ge3$. The input is a **ball instance** as in Theorem 4.1: a well-formed $k$-uniform instance $\mathcal I$ on $n$ variables with at most one unweighted predicate per $k$-set, a center $\tau\in\{0,1\}^n$ and an integer $1\le r\le n$. Write $\mathrm{OPT}_{\tau,r}=\min\{C_{\mathcal I}(x):\mathrm{dist}(x,\tau)\le r\}$ and $D_3(n)=\binom{n-3}{k-3}$.
--
--   There are an absolute constant $C$ and, for every $k\ge3$, constants $\tilde K_k$ and $c_k$ and a deterministic algorithm that runs in time at most $c_k\,2^{c_kr}(n+2)^{Ck}$, i.e. $2^{O_k(r)}n^{O(k)}$, and returns $\hat x$ with
--   $$C_{\mathcal I}(\hat x)\le130\,\mathrm{OPT}_{\tau,r}+\tilde K_k\,D_3(n)\,r^3.\tag{16}$$
--   The output need not lie in the ball.
--
--   This is a deterministic, LP-only alternative to the SDP-based cubic repair of Theorem 4.1, with a constant multiplier in place of $\alpha_k\sqrt{\log(r+2)}$, at the price of a running time exponential in $r$.
--
--   **Formalization Note** The algorithm is a TM2 machine on the encoded ball instance $(\mathcal I,\tau,r)$ that halts within the stated number of steps on every ball instance; the input domain and the reading of $n^{O(k)}$ are those of the published Theorem 4.1 (`theorem_4_1`).
--
--   Differences from the source:
--   - reading: a deterministic 2^{O_k(r)} n^{O(k)}-time algorithm → a TM2 machine on the encoded ball instance halting within c_k · 2^{c_k r} · (n + 2)^{C·k} steps on every ball instance, C absolute (chosen before k), c_k depending on k only; reason: the paper names no machine model; same convention as the published theorem_4_1 for n^{O(k)}
--   - encoding: the ball instance of Theorem 4.1 → a well-formed k-uniform GInst with at most one constraint per scope, τ a list of n bits, 1 ≤ r ≤ n; reason: the input domain of the published theorem_4_1; no instance is added or removed
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Theorem 4.8, p.22 (proof: Lemmas 4.9, 4.10, pp.22–23)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_encInst
import Definitions.Def_AcceptSubcube_coinFrac

namespace AcceptSubcube.Supplement

open AcceptSubcube

/-- **Theorem 4.8 (Parameterized constant-factor repair).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Theorem 4.8, p.22: "For every fixed k ≥ 3 there
is a deterministic 2^{O_k(r)} n^{O(k)}-time algorithm that, given the ball instance of Theorem 4.1,
returns x̂ with C_I(x̂) ≤ 130 OPT_{τ,r} + K̃_k D_3(n) r^3. (16)"

There is an absolute `C` and, for every `k ≥ 3`, constants `K̃_k` and `c_k` and a deterministic
machine on the ball instance `(I, τ, r)` that halts within `c_k · 2^{c_k r} · (n + 2)^{C k}` steps
and whose output `x̂` satisfies (16).

**Formalization Note.** The ball instance of Theorem 4.1 (p.15) is the input domain of the published
`theorem_4_1`: a well-formed `k`-uniform instance with at most one predicate per scope, a center `τ`
(a list of `n` bits) and `1 ≤ r ≤ n`, encoded by `encBall`. `2^{O_k(r)} n^{O(k)}` is read as
`c_k 2^{c_k r} (n + 2)^{C·k}` with `C` absolute (chosen before `k`), the convention of the published
`theorem_4_1`. The output need not lie in the ball. `130` is the paper's absolute constant; `K̃_k`
depends on `k` only. -/
theorem theorem_4_8 :
    ∃ C : ℕ, ∀ k : ℕ, 3 ≤ k →
      ∃ (K : ℝ) (c : ℕ) (alg : GInst × List Bool × ℕ → List Bool),
        ComputesWithinOn
          (fun y : GInst × List Bool × ℕ =>
            y.1.WellFormed ∧ y.1.Uniform k ∧ y.1.ScopeUnique ∧ y.2.1.length = y.1.n ∧
              1 ≤ y.2.2 ∧ y.2.2 ≤ y.1.n)
          encBall encAssign alg (fun y => c * 2 ^ (c * y.2.2) * (y.1.n + 2) ^ (C * k)) ∧
        ∀ I : GInst, I.WellFormed → I.Uniform k → I.ScopeUnique →
          ∀ τ : Fin I.n → Bool, ∀ r : ℕ, 1 ≤ r → r ≤ I.n →
            (cost I (asg I (alg (I, List.ofFn τ, r))) : ℝ) ≤
              130 * (OPTball I τ r : ℝ) + K * (Dj k 3 I.n : ℝ) * (r : ℝ) ^ 3 := by sorry

end AcceptSubcube.Supplement
