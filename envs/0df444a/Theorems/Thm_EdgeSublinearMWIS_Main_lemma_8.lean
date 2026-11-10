-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_lemma_8
-- name    : EdgeSublinearMWIS.Main.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:42:02.317789+00:00
-- url     : https://prove2.me/theorems/dd03a451-57c4-478e-a101-526e61403d4d
-- title:
--   Lemma 8 — light separator or uniform-endpoint path law
-- statement:
--   Let $G$ have $n\ge2$ vertices, let $x\ge0$ be rational with $k=x(V)>0$, and let rational $0<\delta<1$. For integer $\ell\ge c_0\delta^{-1}\log_2n$, a deterministic polynomial-bit-time program returns a $(\delta,x)$-light balanced separator or an induced vertex set $W$, $|W|>2n/3$, and a rational path law satisfying
--   $$\Pr[(\operatorname{first}Q,\operatorname{last}Q)=(u,v)]=|W|^{-2},\qquad \Pr[v\in Q]\le\ell x_v/k.$$
--   The constant $c_0>0$ is universal. This is the entire distributional alternative; endpoints are independent and uniform. The finite law is output explicitly, with polynomial encoded support. The auxiliary $\gamma=\ell n^2/(3k)$ is determined by the supplied data and is not an independent input.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graphs → graphs labeled by Fin n and finite vertex masks; reason: every finite graph admits such a labeling; induced injections transport class membership
--   - encoding: a deterministic polynomial-time algorithm on rational inputs → one finite program, serialized rational inputs and actual halting-step bounds; reason: binary conventions fix a computational model without restricting rational values
--   - encoding: G prime and a path probability distribution → an induced vertex mask and a sparse rational path law; reason: a finite graph has finitely many simple paths; encoded support length is charged
--   - encoding: gamma fixed by Eq. (5) → gamma is omitted as a redundant input and computed from ell,n,k; reason: it is uniquely determined and no source instance is excluded
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Lemma 8, p.8 (PDF p.8), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Paths

namespace EdgeSublinearMWIS.Main

theorem lemma_8 :
    ∃ (M : Program) (c₀ : ℝ) (time : Polynomial ℕ), 0 < c₀ ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode)
        (δ : RationalCode) (ell : ℕ),
        2 ≤ n → (∀ v, 0 ≤ (x v).value) →
        0 < vertexSum (fun v => ((x v).value : ℝ)) Finset.univ →
        0 < δ.value → δ.value < 1 → c₀ * (δ.value : ℝ)⁻¹ * logTwo n ≤ ell →
        ∃ t : ℕ, t ≤ time.eval ((flowInput G x δ ++ encodeNat ell).length + 1) ∧
          ((∃ S : Finset (Fin n),
              Runs M (flowInput G x δ ++ encodeNat ell) (false :: mask S) t ∧
              Light G Finset.univ S δ.value (fun v => ((x v).value : ℝ))) ∨
            ∃ (W : Finset (Fin n)) (f : List (List (Fin n) × ℚ)),
              Runs M (flowInput G x δ ++ encodeNat ell)
                (true :: (mask W ++ encodeSparsePaths f)) t ∧
              PathOutcome G (fun v => ((x v).value : ℝ)) ell W (realPaths f)) := by sorry

end EdgeSublinearMWIS.Main
