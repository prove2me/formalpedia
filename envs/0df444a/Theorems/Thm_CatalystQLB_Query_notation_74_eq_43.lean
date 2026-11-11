-- Prove2me | Theorems.Thm_CatalystQLB_Query_notation_74_eq_43
-- name    : CatalystQLB.Query.notation_74_eq_43
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:24:27.630193+00:00
-- url     : https://prove2.me/theorems/32d326b7-7787-4b0b-a748-07625a23481b
-- title:
--   Notation 74 and Eq. (43) — first-query branch decomposition $U=\sum_{i=1}^{q-1}A_i\Pi Z_i+Z_q$
-- statement:
--   Let an oracle circuit make $q-1$ queries to $O_f$, with segments $V_i$, and fix $f,g,x$. With $\Pi=|g(x)\rangle\langle g(x)|_Q\otimes I_{RC}$ and the operators $Z_i$, $A_i$ of Notation 74:
--   1. the circuit's unitary decomposes as
--   $$U=\sum_{i=1}^{q-1}A_i\,\Pi\,Z_i+Z_q;$$
--   2. each $A_i$ ($1\le i\le q-1$) is unitary;
--   3. each $Z_i$ ($1\le i\le q$) is a contraction, $\|Z_i\|\le1$;
--   4. each $Z_i$ depends on $f$ only through the restriction of $f$ to $\{0,1\}^\lambda\setminus\{g(x)\}$: if $f'$ agrees with $f$ off $g(x)$, then $Z_i$ is the same for $f'$ and $f$.
--
--   Applied to $|x,f(g(x)),0^\ell\rangle$ after $\Pi^{\mathrm{search}}$, item 1 is Eq. (43). The decomposition separates the circuit by the step at which $f$ is first queried at $g(x)$, so that the branch before that query does not see $f(g(x))$.
--
--   **Formalization Note** $\|\cdot\|$ is the operator norm `QAlgorithms.specNorm`. The display of Notation 74 on p.44 prints $A_q$ struck through with $\mathbb I$ above it; the last term is $Z_q$, as in Eqs. (43) and (53).
--
--   Differences from the source:
--   - reading: Notation 74's display, which prints $A_q$ struck through with $\mathbb I$ above it → last term $Z_q$; reason: as in Eqs. (43) and (53), which print $Z_q$
--   - generalization: Eq. (43): the identity applied to $|x,f(g(x)),0^\ell\rangle$ after $\Pi^{\mathrm{search}}$, for $q\ge2$ → the operator identity of Notation 74, for every circuit (for $q=1$ the sum is empty and $U=Z_1=V_1$); reason: the operator identity implies Eq. (43) by applying both sides to the vector; at $q=1$ it is trivially true
--   - encoding: “conditional on $g$, $x$ and the restriction of $f$ to all points other than $g(x)$, every $Z_i$ is independent of $f(g(x))$” → $Z_i$ is equal for any two $f$, $f'$ that agree off $g(x)$; reason: the same statement for a deterministic operator-valued function of $f$
--   - encoding: “$Z_i$ is a contraction” → `specNorm (Z i) ≤ 1`; reason: definition of a contraction in the operator norm
--   - generalization: the proof's standing $\ell=\ell(\lambda)=\lfloor c\lambda\rfloor$ → every $\ell\in\mathbb N$ and every $\lambda$; reason: the display is explicit in $\ell$ and $\lambda$ and its derivation never uses the relation between them; it specializes to the source's $\ell(\lambda)$
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Notation 74, p.44 (PDF 47); Eq. (43), p.45 (PDF 48)

import Mathlib
import Definitions.Def_CatalystQLB_Query_OracleCircuit_branchZ
import Definitions.Def_CatalystQLB_Query_OracleCircuit_branchA

namespace CatalystQLB.Query

open QAlgorithms

/-- **Notation 74 with Eq. (43)**, the first-query branch decomposition (arXiv:2609.40323 (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, version of 2026-11-03), Notation 74, p.44
(PDF 47), and §5.3, p.45 (PDF 48)). Fix `f, g, x`, let `q − 1 = numF C` and
`Π = |g(x)⟩⟨g(x)|_Q ⊗ I_RC`. Then
1. `U = Σ_{i=1}^{q−1} A_i Π Z_i + Z_q`;
2. each `A_i` is unitary;
3. each `Z_i` is a contraction (`‖Z_i‖ ≤ 1`, operator norm);
4. each `Z_i` depends on `f` only through its restriction to `{0,1}^n ∖ {g(x)}`.

**Formalization Note** The operator identity of Notation 74 (Eq. (43) is it applied to
`|x, f(g(x)), 0^ℓ⟩` after `Π^search`); the display on p.44 prints `A_q` struck through with `I`,
i.e. the last term is `Z_q`. Operator norm = `QAlgorithms.specNorm`. -/
theorem notation_74_eq_43 {n ℓ : ℕ} (C : OracleCircuit n ℓ) (f g : Qubits n → Qubits n)
    (x : Qubits n) :
    C.eval f g = (∑ i ∈ Finset.Icc 1 C.numF,
        C.branchA f g i * firstQueryProj (g x) * C.branchZ f g x i) +
      C.branchZ f g x (C.numF + 1) ∧
    (∀ i ∈ Finset.Icc 1 C.numF, C.branchA f g i ∈ Matrix.unitaryGroup (Idx n ℓ) ℂ) ∧
    (∀ i ∈ Finset.Icc 1 (C.numF + 1), specNorm (C.branchZ f g x i) ≤ 1) ∧
    (∀ f' : Qubits n → Qubits n, (∀ y, y ≠ g x → f' y = f y) →
      ∀ i ∈ Finset.Icc 1 (C.numF + 1), C.branchZ f' g x i = C.branchZ f g x i) := by sorry

end CatalystQLB.Query
