-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_Supplement_corollary_4_10
-- name    : CatalyticTreeEval.Main.Supplement.corollary_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:40:34.077764+00:00
-- url     : https://prove2.me/theorems/5398038e-2933-41fa-a165-cc94059de0dd
-- title:
--   Corollary 4.10 (companion theorem; not used in the proof of the goal) — optimal-vector conditional consequence
-- statement:
--   Fix $t\ge2$ distinct odd primes $p_1,\ldots,p_t$ and their product $m$. Suppose there is a sequence of canonical-score matching families in $(\mathbb Z_m)^{d(\ell)}$, of exact size $2^\ell$, such that $d(\ell)\le C_d\ell\log_2(\ell+2)$ for all $\ell\ge1$, and one fixed printer uses at most $C_s\ell$ workspace. The sequence, printer and constants are fixed before varying $\ell$. Then an ordinary deterministic machine evaluates every binary TreeEval instance of input length $n$ with
--   $$S\le C L(n)L_2(n),\qquad T\le C_t(n+1)^q,$$
--   where $q$ is a fixed positive integer. It prints the entire root label and has no catalytic tape. This is the conditional companion theorem corresponding to informal Theorem 1.4; it does not assert existence of the hypothesized sequence.
--
--   Differences from the source:
--   - encoding: asymptotic algorithmic resource bounds → a finite binary machine and positive uniform constants, with fixed polynomial degrees where needed; reason: expands O/poly using actual transitions and visited work cells; constants precede varying inputs and tapes
--   - encoding: log n, log log n and log log log n in asymptotic bounds → L(n)=1+log₂(n+1), L₂(n)=1+log₂ L(n), L₃(n)=1+log₂ L₂(n), with n the full serialized input length; reason: positive-log conventions preserve the stated asymptotics and include every small valid input
--   - encoding: binary parameters and one-based finite indices → self-delimiting binary headers, zero-based Fin indices and the published printer requests; reason: encodes the same finite data with linear bit-length overhead and no change to the space class
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), canonical source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238, Corollary 4.10, printed p. 28 (PDF p. 30)

import Definitions.Def_CatalyticTreeEval_Main_Supplement_UniformConstructions

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

theorem corollary_4_10 (t : ℕ) (p : Fin t → ℕ) (ht : 2 ≤ t) (hp : OddPrimeData p)
    (hQ : ∃ (Q : VectorSequence (modulus p)) (MV : Machine) (Cd Cs : ℝ),
      0 < Cd ∧ 0 < Cs ∧ OptimalSequence p Q MV Cd Cs) :
    ∃ (M : Machine) (Cs Ct : ℝ) (q : ℕ), 0 < Cs ∧ 0 < Ct ∧ 0 < q ∧
      ∀ h l : ℕ, 0 < h → 0 < l → ∀ I : Tree l h,
      PrintsIn M I.encode (bits l I.value.val)
        (Cs * lg I.encode.length * loglog I.encode.length)
        (Ct * ((I.encode.length : ℝ) + 1) ^ q) := by sorry

end CatalyticTreeEval.Main.Supplement
